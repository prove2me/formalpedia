-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_prod_integrable
-- name    : AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_prod_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:36:22.905802+00:00
-- url     : https://prove2.me/theorems/789c5a26-84fe-42c4-9ba8-d2faa4473cbe
-- title:
--   Zero Gaussian q-scale generator Laplace residual under global product integrability
-- statement:
--   For the zero-origin twice-differentiable q-scale function, assume full exponential-weighted derivative and jump integrability and the Gaussian boundary slope normalisation. If the weighted compensated jump kernel is absolutely integrable against the positive-state-by-negative-jump product measure, the generator residual has Laplace transform zero. The product-integrability Fubini theorem supplies the state/jump exchange needed for the already proved full residual transform identity; no unjustified Fubini equality is separately assumed.
-- source:
--   Combination of the proved weighted generator-residual transform and global compensated-kernel Fubini under absolute integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_prod_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1)
    (hkernel : IntegrableOn (fun y : ℝ =>
       Real.exp (θ * y) - 1 -
         θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
       (Iio 0) X.ν)
    (hGint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) *
         ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x))
       (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
           SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
       (Ioi (0 : ℝ)))
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry

end AvramDividend.Classical
