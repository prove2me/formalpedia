-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_abovecap_truncated_generator_positive_lintegral_le_tail_mass
-- name    : AvramDividend.Classical.avram_mix_inf20_original_abovecap_truncated_generator_positive_lintegral_le_tail_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:41:04.51818+00:00
-- url     : https://prove2.me/theorems/c3f99403-43f7-42ae-9a5c-92e32650dcf6
-- title:
--   Original corrected finitecap Lévy actual generator positive lintegral bounded by finite negative mark tail mass
-- statement:
--   Source-faithful true Lévy generator positive-part lintegral estimate above finite cap, correctly compensating jumps only inside (-1,1). The positive part of the source SpectrallyNegativeLevy.generatorIntegrand is dominated by the unit indicator of finite-rate negative tail z≤-δ, by the proven source-faithful pointwise lemma 15371b4c. Integrate with respect to the actual negative-jump Lévy measure X.ν restricted to Iio 0. The exact integral equals the restricted tail mass by pinned Mathlib lintegral_indicator_one, and the latter is finite whenever truncated quadratic Lévy energy holds (Proved 3e5bbc19). This proves a genuine σ-finite compensation control without assuming the Lévy measure has finite first absolute moment, essential for the stopped original mixed-infinite-activity physical generator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_abovecap_truncated_generator_positive_lintegral_le_tail_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ y : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hδcap : δ ≤ C.toReal) (hy : C.toReal < y) :
    (∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal
        (SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
          y z) ∂X.ν) ≤
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) := by sorry
