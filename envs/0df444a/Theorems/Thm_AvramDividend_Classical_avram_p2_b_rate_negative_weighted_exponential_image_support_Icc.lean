-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_exponential_image_support_Icc
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_weighted_exponential_image_support_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:56:10.978615+00:00
-- url     : https://prove2.me/theorems/ec8b8a46-bba3-4474-89aa-ce9fe35ab89a
-- title:
--   Compact support of the fourth-weighted exponential image of negative Levy marks
-- statement:
--   For any real mark measure, nonnegative tilt θ, and fourth-power exponential density on its strictly negative restriction, the exponential image measure is almost surely supported in the compact interval [0,1]. This bridges the source-original Lévy negative-support measure to the support hypothesis in the moment inversion helper.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_withDensity_restrict_negative_ae

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_negative_weighted_exponential_image_support_Icc
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᵐ z ∂(((ν.restrict (Set.Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp (θ * y) - 1) ^ 4))).map
      (fun y => Real.exp (θ * y))), z ∈ Set.Icc (0 : ℝ) 1 := by sorry
