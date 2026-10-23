-- Prove2me | Theorems.Thm_BrumelleMcGill1993_thm2_exists_optimal_integer_policy_faithful
-- name    : BrumelleMcGill1993.thm2_exists_optimal_integer_policy_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:01:17.395435+00:00
-- url     : https://prove2.me/theorems/20020d91-5806-4df0-93e0-326a883ae6cd
-- title:
--   Theorem 2, p. 132, as stated in the paper: integer demands admit an optimal integer protection-level policy
-- statement:
--   Consider a flight whose fare classes $k = 1, 2, \dots$ have independent, nonnegative, integer-valued demands $X_1, X_2, \dots$ and fares $f_1 > f_2 > \cdots > 0$. A protection-level policy is a sequence $p = (p_1, p_2, \dots)$ with $p_k \ge 0$, where $p_k$ seats are protected for the nest of the $k$ highest classes. Let $ER_k[s; p; X]$ be the expected revenue from classes $1, \dots, k$ with $s$ seats under $p$, given by the nested recursion (8)–(9) of the paper. Then there is an integer policy $p^* = (p^*_1, p^*_2, \dots)$, $p^*_k \in \{0, 1, 2, \dots\}$, such that
--
--   $$ER_k[s; q; X] \le ER_k[s; p^*; X] \qquad \text{for every policy } q,\ \text{every } k \ge 1,\ \text{every } s \ge 0.$$
--
--   This is Theorem 2 of Brumelle and McGill (1993) as stated in the paper: with integer demands, optimal protection levels can be taken integral. The existing theorem NestedSeatAlloc.IntPolicy.theorem2_exists_optimal_integer_policy proves this together with the first-order condition $f_{k+1} \in \delta ER_k[p^*_k; p^*; X]$, so this statement is its first conjunct.
--
--   **Formalization Note** Demands are real-valued random variables that take natural-number values at every outcome; $ER_k$ is a Bochner integral, and optimality is over all real-valued policies $q \ge 0$. Fare positivity is stated explicitly; the paper treats fares as positive average revenues and its claim fails without it.
-- source:
--   Brumelle & McGill, Airline Seat Allocation with Multiple Nested Fare Classes, Operations Research 41(1) (1993), doi:10.1287/opre.41.1.127, p. 132, Theorem 2

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem BrumelleMcGill1993.thm2_exists_optimal_integer_policy_faithful {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, IsOptimal P X f (fun k => (p k : ℝ)) := by sorry
