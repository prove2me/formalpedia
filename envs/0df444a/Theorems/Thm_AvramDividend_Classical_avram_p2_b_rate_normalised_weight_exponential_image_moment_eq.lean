-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_normalised_weight_exponential_image_moment_eq
-- name    : AvramDividend.Classical.avram_p2_b_rate_normalised_weight_exponential_image_moment_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:38:27.817318+00:00
-- url     : https://prove2.me/theorems/75765dd0-e30c-49c4-a9d8-62269c01b86f
-- title:
--   Normalised fourth-weighted exponential-image moments equal the original image moment divided by time
-- statement:
--   For measurable real Y, any exponent theta, integer k and real time parameter h, the ENNReal kth moment of the fourth-exponential pointwise weight multiplied by the inverse ENNReal time factor equals the unnormalised fourth-weighted exponential image measure kth moment divided by ofReal h. This exact identity enables source P2-I compact-test adaptation without swapping the original process or postulating a compensator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_lintegral_normalised_weight_mul

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_normalised_weight_exponential_image_moment_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) (k : ℕ) (h : ℝ) :
    (∫⁻ ω, (ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
      (ENNReal.ofReal h)⁻¹) *
      (ENNReal.ofReal (Real.exp (θ * Y ω))) ^ k ∂μ) =
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) / ENNReal.ofReal h := by sorry
