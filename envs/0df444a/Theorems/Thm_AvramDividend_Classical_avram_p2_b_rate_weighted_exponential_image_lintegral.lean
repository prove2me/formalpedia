-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_lintegral
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:20:54.66549+00:00
-- url     : https://prove2.me/theorems/a541be4a-3856-42ec-918c-b59024053183
-- title:
--   Weighted exponential-image pushforward lower moments equal original weighted lower moments
-- statement:
--   For a measurable real random variable Y and any underlying measure, the kth nonnegative power lower integral against the weighted exponential image measure equals the lower integral of the fourth-exponential weight times the kth exponential moment. The image measure uses withDensity of the actual Y-law followed by pushforward, without assuming support negativity or a Lévy jump-rate identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) =
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (θ * Y ω)) ^ k) ∂μ := by sorry
