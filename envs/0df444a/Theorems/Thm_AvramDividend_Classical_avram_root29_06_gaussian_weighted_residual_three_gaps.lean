-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_weighted_residual_three_gaps
-- name    : AvramDividend.Classical.avram_root29_06_gaussian_weighted_residual_three_gaps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:50:31.184433+00:00
-- url     : https://prove2.me/theorems/1e2c8755-c313-46f3-94dc-4effcd7ebe02
-- title:
--   Gaussian weighted generator residual from second derivative, jump integrability and Fubini
-- statement:
--   For a true positive-variance spectrally negative Levy process and its q-scale function, the exponentially weighted generator residual has zero integral whenever weighted second-derivative integrability, weighted jump-integral integrability and the exact Fubini equality hold. The scale transform, weighted first derivative, compensated Levy kernel and correct positive right-origin normalisation are discharged from established source-specific results, without assuming the false ordinary derivative at zero.
-- source:
--   Source-specific reduction of original generator_vcstar_eq_zero 88d146b8 and the Proved right-origin residual bridge f4b9a18c; it isolates three genuinely analytic global prerequisites. The declaration does not claim these prerequisites from IsScaleFunction, nor does it prove full generator harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_integrable_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_generator_origin_normalization_from_right_limit

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_root29_06_gaussian_weighted_residual_three_gaps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDlim : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η))
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
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
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
        q * W x)) = 0 := by sorry
