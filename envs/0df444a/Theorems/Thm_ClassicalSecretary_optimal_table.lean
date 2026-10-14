-- Prove2me | Theorems.Thm_ClassicalSecretary_optimal_table
-- name    : ClassicalSecretary.optimal_table
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:52:20.14851+00:00
-- url     : https://prove2.me/theorems/5a0a7e09-3adc-43a9-8ba1-a4ee8236f38f
-- title:
--   Optimal cutoffs and success probabilities for $n \le 10$
-- statement:
--   For $n = 1,\dots,10$ the cutoff $r_n$ in the table below is optimal, i.e. $P_n(\text{cutoff } r_n) = V_n$, and $V_n$ equals the exact rational value shown. Each value rounds to the decimal entry of the source table.
--
--   | $n$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
--   |---|---|---|---|---|---|---|---|---|---|---|
--   | $r_n$ | 1 | 1 | 2 | 2 | 3 | 3 | 3 | 4 | 4 | 4 |
--   | $V_n$ | $1$ | $\tfrac12$ | $\tfrac12$ | $\tfrac{11}{24}$ | $\tfrac{13}{30}$ | $\tfrac{77}{180}$ | $\tfrac{29}{70}$ | $\tfrac{459}{1120}$ | $\tfrac{341}{840}$ | $\tfrac{3349}{8400}$ |
--   | source | 1.000 | 0.500 | 0.500 | 0.458 | 0.433 | 0.428 | 0.414 | 0.410 | 0.406 | 0.399 |
--
--   These are concrete checks of the model and of the cutoff formula.
--
--   **Formalization Note** The source gives decimals rounded to three places. The statement uses the exact values $\max_{1\le r\le n} P_n(\text{cutoff } r)$ obtained from the cutoff formula. For $n=2$ both $r=1$ and $r=2$ are optimal, and the table lists $r=1$.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy", table of optimal thresholds r and probabilities P for n = 1, …, 10.

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem optimal_table :
    (successProb 1 (cutoffRule 1) = optimalProb 1 ∧ optimalProb 1 = 1) ∧
    (successProb 2 (cutoffRule 1) = optimalProb 2 ∧ optimalProb 2 = 1 / 2) ∧
    (successProb 3 (cutoffRule 2) = optimalProb 3 ∧ optimalProb 3 = 1 / 2) ∧
    (successProb 4 (cutoffRule 2) = optimalProb 4 ∧ optimalProb 4 = 11 / 24) ∧
    (successProb 5 (cutoffRule 3) = optimalProb 5 ∧ optimalProb 5 = 13 / 30) ∧
    (successProb 6 (cutoffRule 3) = optimalProb 6 ∧ optimalProb 6 = 77 / 180) ∧
    (successProb 7 (cutoffRule 3) = optimalProb 7 ∧ optimalProb 7 = 29 / 70) ∧
    (successProb 8 (cutoffRule 4) = optimalProb 8 ∧ optimalProb 8 = 459 / 1120) ∧
    (successProb 9 (cutoffRule 4) = optimalProb 9 ∧ optimalProb 9 = 341 / 840) ∧
    (successProb 10 (cutoffRule 4) = optimalProb 10 ∧ optimalProb 10 = 3349 / 8400) := by sorry

end ClassicalSecretary
