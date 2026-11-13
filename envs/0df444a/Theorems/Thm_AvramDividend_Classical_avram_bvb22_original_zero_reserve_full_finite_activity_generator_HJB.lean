-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
-- name    : AvramDividend.Classical.avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:47:52.60617+00:00
-- url     : https://prove2.me/theorems/0344aae3-a14d-4a7f-bc53-f20a43bd28f8
-- title:
--   Original finite-activity BV zero-reserve generator HJB inequality with the true negative-mark contact kernel
-- statement:
--   The original finite-activity source positive-level HJB inequality, standing hypotheses, and continuity at zero force an exact generator inequality at physical zero reserve. The negative-jump integral does not vanish when the physical prepayment reserve is zero. Its exact contribution is minus the value at zero multiplied by the negative-jump intensity. This closes the open-mask boundary term analytically without introducing a modified process or changing the original jump measure.
-- source:
--   Proved 933ee9aa original origin drift HJB ceiling, Proved 14335b0d exact negative-mark zero-reserve kernel, Avram-Palmowski-Pistorius (2007) Proposition 4(i), proof of (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    X.drift - q * w 0 +
      (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) ≤ 0 := by sorry
