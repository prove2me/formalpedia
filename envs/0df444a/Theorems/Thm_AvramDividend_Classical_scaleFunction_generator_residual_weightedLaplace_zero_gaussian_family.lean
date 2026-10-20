-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_residual_weightedLaplace_zero_gaussian_family
-- name    : AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:35:38.219778+00:00
-- url     : https://prove2.me/theorems/1c2d65aa-76dd-4708-8b99-4cab20a58ebf
-- title:
--   The whole family of weighted Laplace transforms of the Gaussian q-scale generator residual vanishes
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function. Assume the Gaussian normalisation condition (sigma^2/2) * W'(0) = 1, that W vanishes at the origin, and that W is twice differentiable on the positive half-line with continuous right limits at the origin. Assume, for every real parameter theta with 0 <= theta and q < X.psi(theta), the required integrability of the discounted state, derivative, second derivative, Gaussian and drift term, and compensated jump term, together with a justified Fubini interchange over the compensated jump integral. Then for every such parameter the theta-weighted generator residual of W is integrable over the positive half-line and its weighted integral vanishes. This is the whole family of Laplace parameters, not a single one, which is what the uniqueness theorem for the Laplace transform of the generator residual needs; a single parameter does not identify the residual.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_residual_weightedLaplace_zero_gaussian_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hzero : W 0 = 0)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1)
    (hkernel : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun y : ℝ =>
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) X.ν)
    (hDint : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hGint : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x))
        (Ioi (0 : ℝ)))
    (hJint : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
        (Ioi (0 : ℝ)))
    (hfubini : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry

end AvramDividend.Classical
