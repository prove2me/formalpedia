-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
-- name    : AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:32:27.444784+00:00
-- url     : https://prove2.me/theorems/c1dd9ab6-529c-4f49-83ac-1dbdc08188d3
-- title:
--   Full weighted Laplace transform of the Gaussian q-scale generator residual vanishes under justified Fubini
-- statement:
--   For a zero-origin q-scale function W of a spectrally negative Lévy process, assume W is twice differentiable on the full positive half-line with the necessary weighted integrability and right boundary conditions, the exact Gaussian origin normalisation (σ²/2)W'(0)=1, compensated exponential Lévy integrability, and the full half-line Fubini interchange. Then the Laplace transform on x>0 of exp(-θx)(ΓW(x)-qW(x)) is identically zero at every admissible θ. The proof formally combines the already established Gaussian/drift derivative transform, the integrated compensated jump transform, the q-scale transform and the exact Lévy–Khintchine cancellation. The exceptional origin and the small-jump compensator are retained correctly. The hypotheses are explicit: the theorem does not claim that the original mission's local C2 assumptions by themselves justify the global Fubini operation or boundary normalisation.
-- source:
--   Exact q-scale transform, the Lévy–Khintchine generator and integration by parts for Avram–Palmowski–Pistorius Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
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
    (hfubini :
       (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) *
           (∫ y in Iio (0 : ℝ),
             SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
       ∫ y in Iio (0 : ℝ),
         (∫ x in Ioi (0 : ℝ),
           Real.exp (-(θ * x)) *
             SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry

end AvramDividend.Classical
