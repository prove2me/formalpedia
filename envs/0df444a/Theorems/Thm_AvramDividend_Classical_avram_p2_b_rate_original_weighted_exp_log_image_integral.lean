-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_exp_log_image_integral
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_exp_log_image_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:54:13.813514+00:00
-- url     : https://prove2.me/theorems/d0f3c12e-a5af-4d2d-b64b-57c276618037
-- title:
--   Original-space weighted exponential expectations equal image-space weighted logarithmic tests
-- statement:
--   For any measurable real process increment Y on its original probability or finite-measure space and any real rates rho and theta, the integral of exp(rho log z)(exp(theta log z)-1)^4 against the exponential-image law of Y exactly equals the original expectation exp(rho Y)(exp(theta Y)-1)^4. This uses only measurable pushforward, real integral_map, and log(exp y)=y, with no assumed process jump-rate identity or integrability shortcut. Specialising it to the original SpectrallyNegativeLevy X makes the already Proved source derivative usable in the weighted image-measure moment problem.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_exp_log_image_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (ρ θ : ℝ) :
    (∫ z : ℝ, Real.exp (ρ * Real.log z) *
      (Real.exp (θ * Real.log z) - 1) ^ 4
      ∂(μ.map (fun ω => Real.exp (Y ω)))) =
    ∫ ω, Real.exp (ρ * Y ω) *
      (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ := by sorry
