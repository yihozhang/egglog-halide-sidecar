use core::panic;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    io::{self, BufRead, BufReader},
    sync::Arc,
};

use egglog::{
    actions::{Instruction, Load, Program},
    ast::{Expr, Literal, Symbol, DUMMY_SPAN},
    constraint::AllEqualTypeConstraint,
    core::{AtomTerm, GenericAtom, SymbolOrEq},
    sort::{FromSort, StringSort, UnitSort},
    EGraph, PrimitiveLike, TermId, Value,
};

#[derive(Debug)]
struct KeepBest(Arc<StringSort>, Arc<UnitSort>);

impl PrimitiveLike for KeepBest {
    fn name(&self) -> egglog::ast::Symbol {
        "keep-best".into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        AllEqualTypeConstraint::new("keep-best".into(), span.clone())
            .with_all_arguments_sort(self.0.clone())
            .with_output_sort(self.1.clone())
            .into_box()
    }

    fn apply(
        &self,
        values: &[egglog::Value],
        egraph: Option<&mut egglog::EGraph>,
    ) -> Option<egglog::Value> {
        let egraph = egraph.unwrap();

        // every element of terms contain four things
        //   * name of the root variable
        //   * TermDag
        //   * Term
        //   * A vec `is_subterm` showing for each index if that of the TermDag
        //     is a subterm of the actual extracted term.
        //     This keeps the database compact by only inserting meaningful tuples to the database later.
        let mut terms = vec![];
        for value in values {
            // Step 1: Get the root expression
            let root_var = Symbol::load(&self.0, &value);
            let (_root_sort, root) = egraph.eval_expr(&Expr::var_no_span(root_var)).unwrap();
            let (termdag, term) = egraph.extract_value(root);

            // Step 2: Keep only the subterms of the extracted term
            let mut is_subterm = HashSet::<TermId>::default();
            let mut q = VecDeque::<TermId>::default();
            q.push_back(termdag.lookup(&term));
            while !q.is_empty() {
                let curr = q.pop_front().unwrap();
                if is_subterm.contains(&curr) {
                    continue;
                }
                is_subterm.insert(curr);
                if let egglog::Term::App(_, args) = &termdag.nodes[curr] {
                    for arg in args {
                        q.push_back(*arg);
                    }
                }
            }

            terms.push((root_var, termdag, term, is_subterm));
        }

        // Step 3: Clear the egraph
        for (_name, function) in egraph.functions.iter_mut() {
            function.clear();
        }

        for (root_var, termdag, term, is_subterm) in terms.into_iter() {
            // Step 4: Figure out the type of the extracted term
            // Useful for determining which primitive to apply when there are multiple primitives
            let assignment = {
                let mut problem = egglog::constraint::Problem::default();
                let mut atoms = vec![];
                for (termid, term) in termdag.nodes.iter().enumerate() {
                    if !is_subterm.contains(&termid) {
                        continue;
                    }
                    let var =
                        AtomTerm::Var(DUMMY_SPAN.clone(), format!("$halide${termid}$").into());
                    let atom = match term {
                        egglog::Term::Lit(lit) => vec![GenericAtom {
                            span: DUMMY_SPAN.clone(),
                            head: SymbolOrEq::Eq,
                            args: vec![var, AtomTerm::Literal(DUMMY_SPAN.clone(), lit.clone())],
                        }],
                        egglog::Term::Var(_) => {
                            panic!("Extracted program should not contain variables")
                        }
                        egglog::Term::App(head, args) => {
                            let mut args = args
                                .iter()
                                .map(|arg| {
                                    AtomTerm::Var(
                                        DUMMY_SPAN.clone(),
                                        format!("$halide${arg}$").into(),
                                    )
                                })
                                .collect::<Vec<_>>();
                            args.push(AtomTerm::Var(
                                DUMMY_SPAN.clone(),
                                format!("$halide${termid}$").into(),
                            ));
                            vec![GenericAtom {
                                span: DUMMY_SPAN.clone(),
                                head: SymbolOrEq::Symbol(head.clone()),
                                args,
                            }]
                        }
                    };
                    atoms.extend(atom);
                }
                let query = egglog::core::Query { atoms };
                problem.add_query(&query, &egraph.type_info).unwrap();
                problem
                    .solve(|sort| sort.name())
                    .map_err(|e| e.to_type_error())
                    .unwrap()
            };

            // Step 5: insert the optimal program back to the egraph
            let mut termid_to_value_cache = HashMap::<TermId, Value>::default();
            for (termid, term) in termdag.nodes.iter().enumerate() {
                if !is_subterm.contains(&termid) {
                    continue;
                }
                let value = match term {
                    egglog::Term::Lit(literal) => egraph.eval_lit(&literal),
                    egglog::Term::Var(_) => {
                        panic!("Extracted program should not contain variables")
                    }
                    egglog::Term::App(head, args) => {
                        // Step 5.1: Get the args
                        let args = args
                            .iter()
                            .map(|arg| termid_to_value_cache.get(arg).unwrap().clone())
                            .collect::<Vec<_>>();

                        let mut instructions = vec![];

                        // Step 5.2: Load the args to the stack
                        for i in 0..args.len() {
                            instructions.push(Instruction::Load(Load::Subst(i)));
                        }
                        // Step 5.3: Generate Call* instructions for either function or primitive
                        if egraph.functions.contains_key(head) {
                            instructions.push(Instruction::CallFunction(*head, true));
                        } else {
                            let primitives = egraph.type_info.primitives.get(head).unwrap();
                            let mut arg_sorts = args
                                .iter()
                                .map(|arg| egraph.get_sort_from_value(arg).unwrap().clone())
                                .collect::<Vec<_>>();
                            arg_sorts.push(
                                assignment
                                    .0
                                    .get(&AtomTerm::Var(
                                        DUMMY_SPAN.clone(),
                                        format!("$halide${termid}$").into(),
                                    ))
                                    .unwrap()
                                    .clone(),
                            );
                            let mut found = false;
                            for primitive in primitives {
                                if primitive.accept(&arg_sorts, &egraph.type_info) {
                                    instructions.push(Instruction::CallPrimitive(
                                        primitive.clone(),
                                        args.len(),
                                    ));
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                panic!("No primitive found for {:?}", head);
                            }
                        }

                        // Step 5.4: Run the instructions and get the output
                        let mut out = vec![];
                        egraph
                            .run_actions(&mut out, &args, &Program::new(instructions))
                            .unwrap();
                        out.pop().unwrap()
                    }
                };
                termid_to_value_cache.insert(termid, value);
            }
            // Union the root variable with the inserted expression
            // NB: This depends on let-bindings be implemented as function tables
            egraph.functions.get_mut(&root_var).unwrap().insert(
                &[],
                *termid_to_value_cache.get(&termdag.lookup(&term)).unwrap(),
                egraph.timestamp,
            );
        }

        Some(egraph.eval_lit(&Literal::Unit))
    }
}

// test if the current command should be evaluated
fn should_eval(curr_cmd: &str) -> bool {
    let mut count = 0;
    let mut indices = curr_cmd.chars();
    while let Some(ch) = indices.next() {
        match ch {
            '(' => count += 1,
            ')' => {
                count -= 1;
                // if we have a negative count,
                // this means excessive closing parenthesis
                // which we would like to throw an error eagerly
                if count < 0 {
                    return true;
                }
            }
            ';' => {
                // `any` moves the iterator forward until it finds a match
                if !indices.any(|ch| ch == '\n') {
                    return false;
                }
            }
            '"' => {
                if !indices.any(|ch| ch == '"') {
                    return false;
                }
            }
            _ => {}
        }
    }
    count <= 0
}

fn run_command_in_scripting(egraph: &mut EGraph, command: &str) {
    match egraph.parse_and_run_program(None, command) {
        Ok(msgs) => {
            for msg in msgs {
                println!("{msg}");
            }
        }
        Err(err) => {
            log::error!("{err}");
        }
    }
}

fn main() {
    env_logger::Builder::new()
        .filter_level(log::LevelFilter::Info)
        .format_timestamp(None)
        .format_target(false)
        .parse_default_env()
        .init();
    let mut egraph = egglog::EGraph::default();
    let string_sort: Arc<StringSort> = egraph.get_sort_by(|_| true).unwrap();
    let unit_sort: Arc<UnitSort> = egraph.get_sort_by(|_| true).unwrap();
    egraph.add_primitive(KeepBest(string_sort, unit_sort));

    let stdin = io::stdin();
    log::info!("Welcome to Egglog! (sidecar)");

    let mut cmd_buffer = String::new();

    for line in BufReader::new(stdin).lines() {
        match line {
            Ok(line_str) => {
                cmd_buffer.push_str(&line_str);
                cmd_buffer.push('\n');
                // handles multi-line commands
                if should_eval(&cmd_buffer) {
                    run_command_in_scripting(&mut egraph, &cmd_buffer);
                    cmd_buffer = String::new();
                }
            }
            Err(err) => {
                log::error!("{err}");
                std::process::exit(1)
            }
        }
        log::logger().flush();
        if egraph.is_interactive_mode() {
            println!("(done)");
        }
    }

    if !cmd_buffer.is_empty() {
        run_command_in_scripting(&mut egraph, &cmd_buffer)
    }
}
