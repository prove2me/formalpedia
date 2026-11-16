-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_nat_factorial_exp_tsum_20261115
-- name    : AvramDividend.Classical.avram_a25_nat_factorial_exp_tsum_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:37:29.060203+00:00
-- url     : https://prove2.me/theorems/4abb5890-bc67-40fa-bca3-f8e5afd2b912
-- title:
--   Exponential of a natural count equals the descending-factorial exponential series
-- statement:
--   For any natural k and real θ, the sum of (k)_n (exp θ−1)^n/n! equals exp(θk). Rewrite descending factorial as n! times binomial coefficient and cancel n!; then use the already-Proved finite-support binomial exponential tsum 6a87c7f6. This identity is pointwise and needs no probability assumptions.
-- source:
--   Proved 6a87c7f6 and Nat.descFactorial_eq_factorial_mul_choose, Nat factorial positivity.

import Mathlib
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a25_nat_factorial_exp_tsum_20261115 (k : ℕ) (θ : ℝ) :
    (∑' n : ℕ,
      (Nat.descFactorial k n : ℝ) *
        ((Real.exp θ - 1) ^ n / (n.factorial : ℝ))) =
    Real.exp (θ * (k : ℝ)) := by sorry
