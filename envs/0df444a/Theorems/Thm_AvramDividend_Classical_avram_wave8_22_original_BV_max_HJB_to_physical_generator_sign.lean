-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_to_physical_generator_sign
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_to_physical_generator_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:23:02.73782+00:00
-- url     : https://prove2.me/theorems/958592d6-46a7-48bf-a9db-9eaeeabff410
-- title:
--   Original maximum-form HJB implies capped BV physical generator sign
-- statement:
--   For the original spectrally negative Lévy model with bounded variation, the source maximum-form HJB identity and the exact BV generator formula yield the physical drift and jump integral nonpositive on positive capital below the cap C. The formula identity stays an explicit genuine source obligation.
-- source:
--   Original Avram maximum HJB, exact Lévy generator formula on BV, and max ≤ 0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_to_physical_generator_sign {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0)
  (hPhysical : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.generator w y =
      X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)) :
  ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by sorry
