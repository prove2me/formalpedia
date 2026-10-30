-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_weighted_residual_from_product_l1
-- name    : AvramDividend.Classical.avram_root29_06_gaussian_weighted_residual_from_product_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:32:26.741538+00:00
-- url     : https://prove2.me/theorems/3ac325b5-94cd-41a5-b17e-b0476e1977b2
-- title:
--   Gaussian original generator residual family from genuine product L1 and weighted W second derivative
-- statement:
--   A positive-variance Standing spectrally negative Lévy process has integrable zero weighted q-generator residual at every admissible Laplace parameter if its q-scale function has weighted second derivative L1 and its actual compensated negative-jump kernel has weighted product L1. Product L1 discharges both weighted jump-integral L1 and Fubini by previously proved source-specific theorems. The theorem isolates two real analytic global estimates, without asserting either from terminal exponential moments.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; product-integrability-to-Fubini theorems 1b6472d7 and edc159a5, and conditional Gaussian residual family fb720f36.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_residual_family
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_06_gaussian_weighted_residual_from_product_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hD2 : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hprod : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      Integrable (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x))
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry
