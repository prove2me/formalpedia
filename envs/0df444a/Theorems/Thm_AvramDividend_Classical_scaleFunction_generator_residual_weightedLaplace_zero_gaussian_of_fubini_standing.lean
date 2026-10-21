-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini_standing
-- name    : AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T16:28:19.844436+00:00
-- url     : https://prove2.me/theorems/e7d2f7e1-c402-485f-90c4-a7259ec250bc
-- title:
--   The discounted generator residual of the scale function vanishes for every admissible Laplace parameter
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function. Fix an admissible Laplace parameter theta, that is a theta >= 0 with q < X.psi(theta). Suppose the scale function is twice differentiable on the positive half-line, that the discounted scale function, its first derivative, its second derivative and the discounted jump integral are integrable over the positive half-line, that the compensated kernel is integrable over the negative half-line, and that the discounted jump integral may be interchanged with the integration over the negative half-line. Then the discounted generator residual is integrable over the positive half-line and its integral vanishes. This is the general form of the uniqueness step of the analytic core of Lemma 4 of Avram: the vanishing of the discounted generator residual, for every admissible parameter, is what identifies the residual. It differs from the Gaussian form of the same statement, scaleFunction_generator_residual_weightedLaplace_zero_gaussian_family (1c2d65aa), in that the Gaussian origin normalisation (X.sigma ^ 2 / 2) * deriv W 0 = 1 is not assumed: the origin normalisation is a statement about the Gaussian coefficient alone, and the general case is obtained by treating the standing Condition (3.3) case by case, using the positivity of the Gaussian coefficient where it holds and the growth of the Levy exponent elsewhere.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hX : X.Standing)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
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
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
      (Iio 0) X.ν)
    (hfubini :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν)
    (hpsi : X.ψ θ =
      (X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ +
      ∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry

end AvramDividend.Classical
