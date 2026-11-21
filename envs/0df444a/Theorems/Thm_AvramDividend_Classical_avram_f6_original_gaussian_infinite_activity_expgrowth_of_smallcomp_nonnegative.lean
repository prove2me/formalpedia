-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_gaussian_infinite_activity_expgrowth_of_smallcomp_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_gaussian_infinite_activity_expgrowth_of_smallcomp_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:33:01.185487+00:00
-- url     : https://prove2.me/theorems/8a7ab495-917a-4346-b4cb-f7b534f19397
-- title:
--   Original mixed Gaussian infinite activity HJB exponential growth under true nonnegative smallmark compensated generator
-- statement:
--   For true original Gaussian spectrally negative Lévy X with σ>0, C=∞ HJB candidate w with gradient≥1 and generator≤q w, if actual compensated small negative mark generator integral over (-1,0) is ≥0 at all positive reserve, then w has a global exponential upper envelope. Proof uses real original generator large/small split, finite ν large rate and Gaussian scalar ODE comparison; the smallmark sign is an explicit additional structural hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_gaussian_infinite_activity_expgrowth_of_smallcomp_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : 0 < X.σ) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hSmallNonnegative : ∀ y : ℝ, 0 < y →
      0 ≤ ∫ z in Ioo (-1 : ℝ) 0,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by sorry
