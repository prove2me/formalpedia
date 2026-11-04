-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exp_image_polynomial_lintegral
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_exp_image_polynomial_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:50:52.692104+00:00
-- url     : https://prove2.me/theorems/d94f4c44-4146-47a8-9417-1fd43d2e3db9
-- title:
--   All polynomial moments of a weighted exponential-image measure equal original-space weighted moments
-- statement:
--   For an arbitrary measurable real random variable Y and any measurable nonnegative density w on the original space, every nonnegative integer polynomial moment of the weighted exp(Y) pushforward measure is exactly the weighted original-space integral of exp(Y)^k. This rigorous source-independent map/withDensity identity is the measure-theoretic bridge required to turn the already Proved original Lévy weighted exponential small-time derivative into moment convergence of finite exponential-image measures. The theorem makes no Lévy rate assumption.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_exp_image_polynomial_lintegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (w : Ω → ℝ≥0∞) (hw : Measurable w) (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k
      ∂((μ.withDensity w).map (fun ω => Real.exp (Y ω)))) =
    ∫⁻ ω, w ω * (ENNReal.ofReal (Real.exp (Y ω))) ^ k ∂μ := by sorry
