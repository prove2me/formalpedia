-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_finite_grid_closed_lower_interior_generator_sum_nonpos
-- name    : AvramDividend.Classical.avram_bvb23_original_finite_grid_closed_lower_interior_generator_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:22:21.651074+00:00
-- url     : https://prove2.me/theorems/6295520d-8a03-4e36-b255-846ab15cc5f0
-- title:
--   Original BV finite-activity closed-lower-interior source generator contributes nonpositively on every physical monotone finite grid
-- statement:
--   On any finite monotone sampling grid with nonnegative left-reserve strictly below the cap, include reserve exactly zero using the original physical BV generator with the full negative-mark contact kernel. At positive interior reserve use the given original HJB generator inequality. Every sampled source cell generator term is nonpositive after multiplication by positive discount and nonnegative physical interval length. The finite sum therefore contributes nonpositively to the original closed-lower-interior budget, without incorrectly extending the strict open HJB mask to reserve zero.
-- source:
--   Proved source exact origin HJB 0344aae3, original positive-interior generator HJB premise; Avram-Palmowski-Pistorius (2007) Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_finite_grid_closed_lower_interior_generator_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (Z : ℕ → ℝ) (n : ℕ)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1))
    (hZ : ∀ i, 0 ≤ Z i ∧ ENNReal.ofReal (Z i) < C) :
    (∑ i ∈ Finset.range (n + 1),
      Real.exp (-(q * (u i : ℝ))) *
      (if Z i = 0 then
        X.drift - q * w 0 +
          (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)
       else X.generator w (Z i) - q * w (Z i)) *
      ((u (i + 1) : ℝ) - (u i : ℝ))) ≤ 0 := by sorry
