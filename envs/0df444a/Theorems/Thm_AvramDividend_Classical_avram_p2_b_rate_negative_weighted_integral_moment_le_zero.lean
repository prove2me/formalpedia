-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_integral_moment_le_zero
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_weighted_integral_moment_le_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:22:50.969975+00:00
-- url     : https://prove2.me/theorems/b358f485-b45f-4de3-97df-b4c0dacaa092
-- title:
--   Negative Lévy weighted image integer moments are bounded by the zeroth moment
-- statement:
--   For a finite fourth-weighted integral over the negative mark half-line and nonnegative slope theta, all higher positive exponential-image moments are bounded by the zeroth weighted moment. This is the quantitative source-ν support fact needed to drive the positive-increment tail to zero with increasing k. Both integrability hypotheses are explicit; no jump-rate or weak-convergence assumption is made.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_negative_weighted_integral_moment_le_zero
    (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ)
    (hzero : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ)
    (hk : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ) :
    (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
      (Real.exp (θ * y) - 1) ^ 4 ∂μ) ≤
    (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂μ) := by sorry
