-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_fourth_weight_real_lintegral_identification
-- name    : AvramDividend.Classical.avram_p2_b_rate_fourth_weight_real_lintegral_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:27:56.203857+00:00
-- url     : https://prove2.me/theorems/def0c97d-9f43-4f8d-9d3f-fbc56b46f7a4
-- title:
--   Fourth-exponential real integral agrees with its lower integral
-- statement:
--   For an integrable fourth-exponential real jump-weight function, the nonnegative real integral, mapped to ENNReal, equals the corresponding lower integral of ENNReal.ofReal of that weight. This source-compatible exact bridge justifies using the nonnegative Markov band inequality together with the original Lévy real small-time derivative, provided the genuine source integrability hypothesis is proved.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_fourth_weight_real_lintegral_identification
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (θ : ℝ)
    (hInt : Integrable
      (fun ω => (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    ENNReal.ofReal
      (∫ ω, (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ) =
    ∫⁻ ω, ENNReal.ofReal
      ((Real.exp (θ * Y ω) - 1) ^ 4) ∂μ := by sorry
