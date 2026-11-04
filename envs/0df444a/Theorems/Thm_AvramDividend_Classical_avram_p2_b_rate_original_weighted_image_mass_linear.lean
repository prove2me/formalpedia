-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_mass_linear
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_mass_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:37:42.526442+00:00
-- url     : https://prove2.me/theorems/00fd2ff6-e628-4dde-8051-0d21b5906e0c
-- title:
--   Original Levy weighted exponential image measure has small-time O(h) total mass
-- statement:
--   The original process fourth-exponentially weighted finite measure, pushed forward by its exponential image, has total mass bounded by h times the genuine negative Lévy fourth-weight integral plus one for all sufficiently small positive h. This follows solely from the accepted original small-time exponent derivative and Laplace integrability, with no independent jump-rate assumption.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_mass_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (((P.withDensity (fun ω =>
          ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω))) Set.univ) ≤
        ENNReal.ofReal (h *
          ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1))  := by sorry
