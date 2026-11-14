-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_zero_or_positive_reserve_corrected_HJB_v2
-- name    : AvramDividend.Classical.avram_bvb23_original_zero_or_positive_reserve_corrected_HJB_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:21:23.772855+00:00
-- url     : https://prove2.me/theorems/bfd0b94c-7f95-45e7-be9a-48e2156032f0
-- title:
--   Original finite activity BV HJB sign covers zero-contact and every strictly positive interior reserve
-- statement:
--   For the original spectrally negative finite-activity bounded-variation source, the correct physical HJB sign is nonpositive at every reserve in the closed lower interior of the admissible cap. Positive reserve uses the original source generator hypothesis; reserve exactly zero uses physical drift, discount, and the nonvanishing original negative-mark kernel. The zero case must not be replaced by the strict interior mask.
-- source:
--   Original positive-interior HJB assumption plus the source-exact corrected origin HJB 0344aae3; Avram-Palmowski-Pistorius Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_zero_or_positive_reserve_corrected_HJB_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) (hz : 0 ≤ z) (hzC : ENNReal.ofReal z < C) :
    (if z = 0 then
      X.drift - q * w 0 +
        (∫ v in Iio (0 : ℝ), w ((0 : ℝ) + v) - w 0 ∂X.ν)
    else X.generator w z - q * w z) ≤ 0 := by sorry
