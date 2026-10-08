-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope
-- name    : AvramDividend.Classical.scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T11:46:25.454452+00:00
-- url     : https://prove2.me/theorems/f4b9a18c-42ed-4881-87ce-e1bcc9a9deaa
-- title:
--   Full weighted generator residual transform with the correct right-hand Gaussian boundary slope
-- statement:
--   For a zero-origin q-scale function with a finite right-hand derivative limit η, under stated global weighted integrability of W, W', W'', and the compensated jump term, the legitimate Fubini interchange and Lévy–Khintchine representation, and the Gaussian normalisation (σ²/2)η=1, the Laplace-weighted integral of the generator residual is zero. The proof combines the right-slope Gaussian drift transform, the fully compensated negative-jump transform, and algebraic cancellation. Unlike earlier ordinary-derivative formulations, it does not conflate Lean's deriv W 0 with the positive-side derivative. The result remains conditional on the strong global analytic assumptions and does not establish pointwise harmonicity from a single transform.
-- source:
--   Avram, Palmowski and Pistorius q-scale generator analysis; pinned accepted weighted Gaussian/drift and compensated Lévy transform identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ σ c η : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDlim : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η))
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
    (hzero : W 0 = 0)
    (horigin : (σ ^ 2 / 2) * η = 1)
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
      (σ ^ 2 / 2) * θ ^ 2 + c * θ +
        (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 -
            θ * (y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν)) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x +
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
          - q * W x)) = 0 := by sorry

end AvramDividend.Classical
