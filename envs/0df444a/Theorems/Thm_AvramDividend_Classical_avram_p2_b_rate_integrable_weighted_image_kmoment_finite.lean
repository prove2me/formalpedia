-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_integrable_weighted_image_kmoment_finite
-- name    : AvramDividend.Classical.avram_p2_b_rate_integrable_weighted_image_kmoment_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:25:24.056869+00:00
-- url     : https://prove2.me/theorems/f2e1dd83-c531-4e70-bb94-4433f7b190b2
-- title:
--   Weighted exponential image has finite kth power lower moment from integrability
-- statement:
--   If an arbitrary measurable real random variable Y has integrable fourth-weighted kth exponential moment, its weighted exponential-image measure has finite kth power lower moment. This supplies the actual finite-measure tightness and uniform-integrability premise for the original Levy process and handles positive increments without sign restrictions or jump-rate hypotheses.

import Mathlib
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_integrable_weighted_image_kmoment_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (θ : ℝ) (k : ℕ)
    (hInt : Integrable (fun ω =>
      (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) < ⊤ := by sorry
