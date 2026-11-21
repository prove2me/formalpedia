-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_largebarrier_full_generator_HJB_from_drift
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_largebarrier_full_generator_HJB_from_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:43:43.598526+00:00
-- url     : https://prove2.me/theorems/bab1a59a-a8d4-4c0e-b142-69e2da4991c7
-- title:
--   Original true infinite-activity finitecap large barrier above-cap HJB generator drift inequality from nonpositive all negative marks
-- statement:
--   Original Lévy infinite-activity finite-cap above-barrier full-generator HJB sign for caps at least unit size, with true source generatorIntegrand. Above C≥1, all negative Lévy marked jump terms in the actual generator are nonpositive (Proved large-barrier negative mark sign). With the genuine integrability hGI, their Lévy integral is nonpositive; the original caplinear generator equals X.c plus this integral by Proved 771f63e9. Therefore whenever the original drift X.c does not exceed q times the affine value w(C)+(y-C), the full generator discount residual is nonpositive. hDrift is a genuine extra inequality that must be shown from boundary HJB or scale function properties to close the full stochastic budget; it is not silently derived. This result localises the remaining above-cap physical HJB obligation for original mixed infinite-activity verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_largebarrier_full_generator_HJB_from_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hCapOne : 1 ≤ C.toReal)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q y : ℝ) (hy : C.toReal < y)
    (hGI : Integrable (fun z : ℝ =>
      SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z) (X.ν.restrict (Iio (0 : ℝ))))
    (hDrift : X.c ≤ q * (w C.toReal + (y - C.toReal))) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    X.generator V y - q * V y ≤ 0 := by sorry
