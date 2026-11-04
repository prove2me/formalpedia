-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:30:14.653908+00:00
-- url     : https://prove2.me/theorems/c775f110-bd94-42bc-979a-3b58cbf814c9
-- title:
--   Original BV maximum HJB gives exact physical generator sign without surrogate formula
-- statement:
--   For the true source spectrally negative Lévy BV process, the original generator integrability and max HJB equality imply exact physical drift-plus-negative-jump-minus-discount nonpositivity on positive capital below C, by an existing accepted generator representation theorem. No extra physical equality hypothesis.
-- source:
--   Proved boundedVariation_generator_physical_drift_representation and original maximum-HJB.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
  ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by sorry
