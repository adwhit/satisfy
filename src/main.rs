use clap::Parser;
use std::path::{Path, PathBuf};

use anyhow::{bail, Result};

#[derive(Parser)]
struct Args {
    cnf: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let cnf = read_cnf_from_file(args.cnf)?;
    match Solver::new(cnf).solve() {
        Some(res) => {
            println!("SAT");
            for r in res {
                print!("{r} ");
            }
        }
        None => println!("UNSAT"),
    }
    Ok(())
}

struct Clause {
    literals: Vec<i16>,
}

struct Cnf {
    n_vars: u16,
    clauses: Vec<Clause>,
}

fn read_cnf_from_file(path: impl AsRef<Path>) -> Result<Cnf> {
    let file = std::fs::read_to_string(path)?;
    parse_cnf(&file)
}

fn parse_cnf(file: &str) -> Result<Cnf> {
    let mut in_header = true;
    let mut n_vars = 0;
    let mut n_clauses = 0;
    let mut clauses = Vec::new();
    for line in file.lines() {
        let line = line.trim();
        if line.starts_with('c') || line.is_empty() {
            // it' s a comment
            continue;
        }
        let mut parts = line.split_whitespace();
        if in_header {
            let Some("p") = parts.next() else {
                bail!("expected 'p' in header")
            };
            let Some("cnf") = parts.next() else {
                bail!("expected 'cnf' in header")
            };
            let Some(nvars) = parts.next() else {
                bail!("expected nVars in header")
            };
            n_vars = nvars.parse::<u16>()?;
            let Some(nclauses) = parts.next() else {
                bail!("expected nClauses in header")
            };
            n_clauses = nclauses.parse::<usize>()?;
            in_header = false
        } else {
            if line.starts_with("%") {
                // we're done, apparently
                break;
            }
            let mut lits: Vec<_> = parts
                .map(|part| part.parse::<i16>())
                .collect::<std::result::Result<_, _>>()?;
            let Some(0) = lits.pop() else {
                bail!("expected clause to end in zero")
            };
            // clauses are always sorted
            lits.sort_by_key(|k| k.abs());
            clauses.push(Clause { literals: lits })
        }
    }
    if clauses.len() != n_clauses {
        bail!("expected {n_clauses} clauses, found {}", clauses.len())
    }
    let max_var = clauses.iter().fold(0, |acc, clause| {
        acc.max(
            clause
                .literals
                .iter()
                .fold(0, |acc, v| acc.max(v.abs() as usize)),
        )
    });
    if (n_vars as usize) < max_var {
        bail!("expected {n_vars} vars, found {max_var}")
    }
    Ok(Cnf { n_vars, clauses })
}

struct Solver {
    clauses: Vec<Clause>,
    var_lookup: Vec<Vec<usize>>,
}

impl Solver {
    fn new(cnf: Cnf) -> Self {
        let mut var_lookup: Vec<Vec<usize>> = std::iter::repeat(Vec::new())
            .take(cnf.n_vars as usize)
            .collect();

        for (ix, c) in cnf.clauses.iter().enumerate() {
            for lit in &c.literals {
                var_lookup[lit.abs() as usize - 1].push(ix)
            }
        }
        Solver {
            clauses: cnf.clauses,
            var_lookup,
        }
    }

    fn n_vars(&self) -> usize {
        self.var_lookup.len()
    }

    fn solve(&mut self) -> Option<Vec<i16>> {
        let assigned: Vec<Assign> = std::iter::repeat(Assign::Unassigned)
            .take(self.n_vars())
            .collect();

        let mut assignment = Assignment {
            assigned,
            trail: Vec::new(),
        };
        'solve: loop {
            // println!("assignment: {assignment:?}");
            match self.check_and_propagate(&assignment) {
                Some(propagations) => {
                    if propagations.is_empty() {
                        // make a decision
                        for v in 1..self.n_vars() + 1 {
                            if let Assign::Unassigned = assignment.assigned[v - 1] {
                                assignment.add_decision(v as i16);
                                continue 'solve;
                            }
                        }
                        // We're done!!
                        let out = (1..self.n_vars() + 1)
                            .map(|v| match assignment.assigned[v - 1] {
                                Assign::Unassigned => unreachable!(),
                                Assign::True => v as i16,
                                Assign::False => v as i16 * -1,
                            })
                            .collect();

                        return Some(out);
                    } else {
                        // println!("Got propagations {propagations:?}");
                        if !assignment.add_propagations(propagations) {
                            // propagations are contradictory
                            if !self.backtrack(&mut assignment) {
                                return None;
                            }
                        }
                    }
                }
                None => {
                    // failed!
                    if !self.backtrack(&mut assignment) {
                        return None;
                    }
                }
            }
        }
    }

    fn check_and_propagate(&self, assign: &Assignment) -> Option<Vec<UnitPropagate>> {
        let latest = assign.latest_assignment();
        if latest.is_empty() {
            check_clauses_and_propagate(assign, self.clauses.iter().enumerate())
        } else {
            let iter = latest.iter().flat_map(|l| {
                self.var_lookup[l.abs() as usize - 1]
                    .iter()
                    .map(|ix| (*ix, &self.clauses[*ix]))
            });
            check_clauses_and_propagate(assign, iter)
        }
    }

    fn backtrack(&mut self, assign: &mut Assignment) -> bool {
        // println!("Backtrack!");
        while let Some(pop) = assign.pop() {
            match pop {
                Action::Decision(lit) => {
                    if lit > 0 {
                        assign.add_decision(lit * -1);
                        return true;
                    }
                }
                Action::UnitPropagate(_) => {}
            }
        }
        false
    }
}

fn check_clauses_and_propagate<'a>(
    assign: &Assignment,
    clauses: impl Iterator<Item = (usize, &'a Clause)>,
) -> Option<Vec<UnitPropagate>> {
    let mut propagations = Vec::new();
    'clause: for (clause_ix, clause) in clauses {
        let mut unit = None;
        let mut seen_true = false;
        for &lit in &clause.literals {
            match assign.assigned[lit.abs() as usize - 1] {
                Assign::Unassigned => {
                    if let None = unit {
                        unit = Some(lit)
                    } else {
                        // at least two unassigned vars, cannnot unit-propagate
                        continue 'clause;
                    }
                }
                Assign::True => {
                    if lit >= 0 {
                        seen_true = true
                    }
                }
                Assign::False => {
                    if lit < 0 {
                        seen_true = true
                    }
                }
            }
        }
        if seen_true {
            // we are fine, carry on
            continue;
        } else {
            if let Some(unit) = unit {
                // we have a unit-propagation!
                propagations.push(UnitPropagate {
                    clause: clause_ix,
                    lit: unit,
                });
            } else {
                // we are not unit and the clause is false,
                // so - assignment has failed!
                return None;
            }
        }
    }
    // if we get this far, all is well
    Some(propagations)
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Assign {
    Unassigned,
    True,
    False,
}

#[derive(Clone, Debug)]
enum Action {
    Decision(i16),
    UnitPropagate(Vec<UnitPropagate>),
}

#[derive(Copy, Clone, Debug)]
struct UnitPropagate {
    clause: usize,
    lit: i16,
}

#[derive(Clone, Debug)]
struct Assignment {
    assigned: Vec<Assign>,
    trail: Vec<Action>,
}

impl Assignment {
    fn latest_assignment(&self) -> Vec<i16> {
        match self.trail.last() {
            Some(Action::Decision(lit)) => vec![*lit],
            Some(Action::UnitPropagate(props)) => props.iter().map(|p| p.lit).collect(),
            None => vec![],
        }
    }

    fn add_propagations(&mut self, mut props: Vec<UnitPropagate>) -> bool {
        props.sort_by_key(|k| k.lit.abs());
        for pairs in props.windows(2) {
            let l = pairs[0];
            let r = pairs[0];
            if l.lit.abs() == r.lit.abs() && l.lit != r.lit {
                // contradiction
                return false;
            }
        }
        for p in &props {
            assert!(p.lit != 0);
            let to_assign = if p.lit > 0 {
                Assign::True
            } else {
                Assign::False
            };
            self.assigned[p.lit.abs() as usize - 1] = to_assign;
        }
        self.trail.push(Action::UnitPropagate(props));
        true
    }

    fn add_decision(&mut self, decision: i16) {
        assert_eq!(
            self.assigned[decision.abs() as usize - 1],
            Assign::Unassigned
        );
        self.assigned[decision.abs() as usize - 1] = if decision < 0 {
            Assign::False
        } else {
            Assign::True
        };

        self.trail.push(Action::Decision(decision))
    }

    fn pop(&mut self) -> Option<Action> {
        let pop = self.trail.pop();
        match pop {
            Some(Action::Decision(lit)) => {
                self.assigned[lit.abs() as usize - 1] = Assign::Unassigned;
            }
            Some(Action::UnitPropagate(ref props)) => {
                for p in props.iter() {
                    self.assigned[p.lit.abs() as usize - 1] = Assign::Unassigned;
                }
            }
            None => {}
        };
        // println!("popped - {pop:?}\nafter pop: {self:?}");
        pop
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve(s: &str) -> Vec<i16> {
        let cnf = parse_cnf(s).unwrap();
        Solver::new(cnf).solve().unwrap()
    }

    fn solve_file(p: impl AsRef<Path>) {
        let cnf = read_cnf_from_file(p).unwrap();
        Solver::new(cnf).solve().expect("expected SAT, got UNSAT");
    }

    fn unsolve(s: &str) {
        let cnf = parse_cnf(s).unwrap();
        if let Some(res) = Solver::new(cnf).solve() {
            panic!("SAT: {res:?}");
        }
    }

    #[test]
    fn test_parse_cnf() {
        let cnf = parse_cnf(
            "
            p cnf 2 2
            -1 2 0
            1 -2 0
            ",
        )
        .unwrap();
        assert_eq!(cnf.n_vars, 2)
    }

    #[test]
    fn test_parse_bad_cnf() {
        assert!(parse_cnf(
            "
            p cnf 2 2
            -1 2 0
            ",
        )
        .is_err());
    }

    #[test]
    fn test_load_cnf() {
        let cnf = read_cnf_from_file("aim-100-1_6-no-1.cnf").unwrap();
        assert_eq!(cnf.n_vars, 100)
    }

    #[test]
    fn test_solve_trivial() {
        let res = solve(
            "
            p cnf 1 0
            ",
        );
        assert_eq!(res, &[1]);
    }

    #[test]
    fn test_solve_simple_1() {
        let res = solve(
            "
            p cnf 1 1
            1 0
            ",
        );
        assert_eq!(res, &[1]);
    }

    #[test]
    fn test_solve_simple_n1() {
        let res = solve(
            "
            p cnf 1 1
            -1 0
            ",
        );
        assert_eq!(res, &[-1]);
    }

    #[test]
    fn test_unsolve_simple() {
        unsolve(
            "
            p cnf 1 2
            -1 0
            1 0
            ",
        )
    }

    #[test]
    fn test_solve_2() {
        let res = solve(
            "
            p cnf 2 2
            1 2 0
            -1 2 0
            ",
        );
        assert_eq!(res, &[1, 2]);
    }

    #[test]
    fn test_solve_2x10() {
        let res = solve(
            "
            p cnf 2 10
            1 2 0
            1 2 0
            1 2 0
            1 2 0
            1 2 0
            -1 2 0
            -1 2 0
            -1 2 0
            -1 2 0
            -1 2 0
            ",
        );
        assert_eq!(res, &[1, 2]);
    }

    #[test]
    fn test_solve_5x0() {
        let res = solve(
            "
            p cnf 5 0
            ",
        );
        assert_eq!(res, &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_solve_3() {
        let res = solve(
            "
            p cnf 3 3
            -1 -2 -3 0
            2 0
            3 0
            ",
        );
        assert_eq!(res, &[-1, 2, 3]);
    }

    #[test]
    fn test_solve_backtrack_2() {
        let res = solve(
            "
            p cnf 2 2
            -1 2 0
            -1 -2 0
            ",
        );
        assert_eq!(res, &[-1, 2]);
    }

    #[test]
    fn test_unsolve_tut() {
        let res = solve(
            "
            p cnf 5 6
            1 -2 0
            1 -3 -4 0
            -1 -3 -4 0
            -3 -5 0
            -3 5 0
            3 4 0
            ",
        );
        assert_eq!(res, &[1, 2, -3, 4, 5])
    }

    #[test]
    fn test_solve_m() {
        let res = solve(
            "
            p cnf 9 6
            1 6 7 8 0 
            2 0
            3 5 0
            4 0
            9 0
            -2 -3 0
            ",
        );
        assert_eq!(res, &[1, 2, -3, 4, 5, 6, 7, 8, 9])
    }

    use test_case::test_case;

    // #[test_case(1)]
    // #[test_case(2)]
    // #[test_case(3)]
    // #[test_case(4)]
    // #[test_case(5)]
    // #[test_case(6)]
    // #[test_case(7)]
    // #[test_case(8)]
    // #[test_case(9)]
    // #[test_case(10)]
    // #[test_case(11)]
    // #[test_case(12)]
    // #[test_case(13)]
    // #[test_case(14)]
    // #[test_case(15)]
    // #[test_case(16)]
    // #[test_case(17)]
    // #[test_case(18)]
    // #[test_case(19)]
    // #[test_case(20)]
    // fn test_solve_benchmark(n: u8) {
    // // download these files from
    // // https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
    //     let file = dbg!(format!("uf20-91/uf20-0{n}.cnf"));
    //     solve_file(file);
    // }
}
