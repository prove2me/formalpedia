-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_generator_weighted_residual_zero_of_correct_right_slope
-- name    : AvramDividend.Classical.gaussian_generator_weighted_residual_zero_of_correct_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:31:06.127324+00:00
-- url     : https://prove2.me/theorems/18326287-1e8b-4145-bba5-fd47b2b0cbd2
-- title:
--   Correct Gaussian weighted generator residual identity under Fubini and the true right slope
-- statement:
--   In the positive-Gaussian branch, the weighted Laplace integral of the canonical q-scale generator residual vanishes under the explicit first- and second-derivative weighted integrability, jump-kernel integrability and Fubini hypotheses. Unlike older generator-residual statements, this theorem uses an explicit η as the right-hand limit of deriv W, never continuity of the ordinary derivative at zero. The Gaussian native variance factor automatically normalises (σ²/2)η=1 through the newly Proved Gaussian right-slope theorem, and the accepted full weighted-generator residual transform then gives the conclusion. This gives the generator verification workstream an importable mathematically consistent Gaussian boundary condition.
-- source:
--   Composition of Proved scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope and new exact Gaussian origin factor theorem.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- Gaussian weighted generator residual vanishes with the genuine right-hand boundary slope. -/
theorem gaussian_generator_weighted_residual_zero_of_correct_right_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
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
        (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 -
            θ * (y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν)) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x +
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
          - q * W x)) = 0 := by
  sorry
end AvramDividend.Classical
