-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_weighted_generator_residual_integral_zero_of_full_fubini
-- name    : AvramDividend.Classical.scaleFunction_weighted_generator_residual_integral_zero_of_full_fubini
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T11:17:18.436796+00:00
-- url     : https://prove2.me/theorems/36fd0513-fd80-4559-9e24-82571c27a7da
-- title:
--   Full q-scale Lévy generator residual has zero weighted Laplace integral under explicit global analytic hypotheses
-- statement:
--   Assume a zero-origin q-scale function W whose exponentially weighted first and second derivatives and integrated jump generator are integrable, with enough differentiability to apply integration by parts. Assume full positive-half-line Fubini for the compensated jump kernel, the Lévy–Khintchine identity for ψ(θ), and the Gaussian boundary slope normalisation (σ²/2)W'(0)=1. Then for θ≥0 and ψ(θ)>q, the weighted integral of the complete generator residual ΓW−qW over x>0 equals zero. This directly combines the proved iterated-derivative Gaussian/drift Laplace formula, the proved integrated compensated-jump Laplace transform, the q-scale transform and the algebraic cancellation theorem. All global analytic assumptions are stated explicitly: the original mission's merely local C2 hypothesis does not justify them by itself.
-- source:
--   Accepted q-scale shifted transform, integrated compensated negative jump formula, Gaussian/drift iterated-derivative transform and exact Lévy–Khintchine cancellation; boundary and Fubini hypotheses explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_weighted_generator_residual_integral_zero_of_full_fubini
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
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hkernel : IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y)) (Iio 0) X.ν)
    (hfubini :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν)
    (hzero : W 0 = 0)
    (hψ : X.ψ θ =
      (X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ +
      ∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry

end AvramDividend.Classical
