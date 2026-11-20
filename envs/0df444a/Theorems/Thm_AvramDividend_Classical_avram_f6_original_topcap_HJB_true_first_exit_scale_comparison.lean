-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_HJB_true_first_exit_scale_comparison
-- name    : AvramDividend.Classical.avram_f6_original_topcap_HJB_true_first_exit_scale_comparison
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T21:05:46.150393+00:00
-- url     : https://prove2.me/theorems/62258405-f5c3-4f87-aef2-84605a4a1993
-- title:
--   Original nonzero-jump topcap HJB killed first-exit comparison with true q-scale function
-- statement:
--   For the exact original standing UBV spectrally negative Lévy X, q>0, topcap HJB supersolution w≥0 with generator≤q w and gradient≥1, construct a true source q-scale W and finite A≥0 such that for every y≥1, w(y)≤A W(y). The stochastic source is the killed two-sided first passage q-supermartingale/optional stopping inequality for w, together with the genuine scale ratio. No fictitious martingale or exogenous domination premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_HJB_true_first_exit_scale_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y := by sorry
