-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_measure_positive_first_moment_tail
-- name    : AvramDividend.Classical.avram_p2_b_rate_finite_measure_positive_first_moment_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:08:26.675326+00:00
-- url     : https://prove2.me/theorems/99e620e1-d7b6-4d8e-8353-9e26ad1c772a
-- title:
--   Quantitative Markov right-tail bound for finite weighted exponential-image measures
-- statement:
--   For any Borel measure on the real line and a positive threshold, the first nonnegative moment bounds the measure of the positive right tail: R times mu([R,infinity)) is at most the integral of the positive part of z. This reusable deterministic inequality is the tightness input for the original rescaled weighted exp(X_h) image using its already Proved first-moment convergence.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_finite_measure_positive_first_moment_tail
    (μ : Measure ℝ) (R : ℝ) (hR : 0 < R) :
    ENNReal.ofReal R * μ (Ici R) ≤
      ∫⁻ z : ℝ, ENNReal.ofReal z ∂μ := by sorry
