-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_all_moments_integrable
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_weighted_all_moments_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:33:17.52411+00:00
-- url     : https://prove2.me/theorems/2e9888f7-25a0-4e75-900f-9d360dddf68a
-- title:
--   Negative fourth-weight integrability dominates every exponential image moment
-- statement:
--   On the negative-mark half-line and any nonnegative exponential slope, integrability of the fourth-weighted Lévy measure kernel implies integrability of all its positive exponential-image integer moments. The proof uses positive image ≤1 and integrability domination; this discharges the kth moment integrability side condition needed for the P2-B Lévy measure domination theorem.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_negative_weighted_all_moments_integrable
    (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ)
    (hzero : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ) :
    IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ := by sorry
