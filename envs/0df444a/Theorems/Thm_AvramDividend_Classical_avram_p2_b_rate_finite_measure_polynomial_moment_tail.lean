-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_measure_polynomial_moment_tail
-- name    : AvramDividend.Classical.avram_p2_b_rate_finite_measure_polynomial_moment_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:45:23.97887+00:00
-- url     : https://prove2.me/theorems/68017068-bf6b-4ef7-a0f3-8d18d6621176
-- title:
--   Arbitrary higher positive-part moment controls the right tail of a measure
-- statement:
--   A source-independent Markov inequality at every nonnegative integer moment k. On the positive tail [R,infinity), the kth nonnegative moment dominates R^k times the tail mass. This is the uniform-integrability and tightness estimate used in the finite-measure method-of-moments bridge for the original weighted Lévy exponential image; it does not assume convergence or any Lévy rate identity.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_finite_measure_polynomial_moment_tail
    (μ : Measure ℝ) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (ENNReal.ofReal R) ^ k * μ (Ici R) ≤
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ := by sorry
