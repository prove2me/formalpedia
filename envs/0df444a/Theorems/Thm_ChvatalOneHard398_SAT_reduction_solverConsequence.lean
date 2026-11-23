-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_reduction_solverConsequence
-- name    : ChvatalOneHard398.SAT.reduction_solverConsequence
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:22:17.727832+00:00
-- url     : https://prove2.me/theorems/1184d337-e250-468e-987e-2a47711f68c6
-- title:
--   Replacing the oracle by a polynomial-time solver
-- statement:
--   Suppose there is a deterministic polynomial-time oracle reduction from bounded distance decoding with factor $1/(4n^{5/2})$ to satisfiability under the rank-one, three-literal promise. Then every total deterministic polynomial-time satisfiability solver that is correct on exactly that target promise can be substituted for the oracle to obtain a total deterministic polynomial-time BDD solver.
--
--   This is the consequence asserted in the second sentence of Theorem C. The substitution composes the reduction's polynomial-time next-step map with the solver, replays the solver's Boolean answers as the oracle history, and uses the fixed polynomial round bound to obtain one polynomial running-time bound. Correctness is required only on BDD inputs satisfying the promise.
--
--   **Formalization Note** In the platform encoding, this is precisely the implication from `BDDReduction TargetPromise` to `SolverConsequence`; oracle calls have unit cost and output is a list of rational coordinates.
-- source:
--   Alberto Del Pia, STOC 2027 submission #398, p.7 Theorem C second sentence, p.8 promise-problem oracle conventions, and p.29 proof of Theorem C; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle

theorem ChvatalOneHard398.SAT.reduction_solverConsequence : ChvatalOneHard398.SAT.BDDReduction ChvatalOneHard398.SAT.TargetPromise → ChvatalOneHard398.SAT.SolverConsequence := by sorry
