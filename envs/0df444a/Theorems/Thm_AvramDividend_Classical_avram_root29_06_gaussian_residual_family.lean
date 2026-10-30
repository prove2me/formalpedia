-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_residual_family
-- name    : AvramDividend.Classical.avram_root29_06_gaussian_residual_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:06:26.364985+00:00
-- url     : https://prove2.me/theorems/fb720f36-c8c3-4c92-a804-b070970e7584
-- title:
--   Full Gaussian weighted generator residual family from three global estimates
-- statement:
--   For any genuine Standing spectrally negative Levy process with positive Gaussian variance, every admissible Laplace parameter has integrable exponentially weighted original generator residual with zero integral, provided weighted second scale derivative integrability, jump integral integrability and justified compensated-jump Fubini hold uniformly in the parameter. All local C2, origin/right-slope, first-derivative and algebraic assumptions are discharged by already proved canonical facts.
-- source:
--   Original generator_vcstar_eq_zero Gaussian branch; composes the newly Proved Gaussian fixed-theta residual bridge 1e2c8755, true source C2 f596d402, origin zero 20b1acb4, right slope 62495c30 and weighted W' a01f741d. This theorem identifies exactly three unproved global analytic families, not a terminal-moment shortcut.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_weighted_residual_three_gaps
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_root29_06_gaussian_residual_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hD2 : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hJ : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
        (Ioi (0 : ℝ)))
    (hF : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x))
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry
