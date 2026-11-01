-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_residual_from_eventual_product
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_residual_from_eventual_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:18:50.389981+00:00
-- url     : https://prove2.me/theorems/ac3d964b-8034-470f-ac38-3983b6e71262
-- title:
--   Gaussian q-scale source generator residual vanishes at high Laplace weights from actual compensated product L1
-- statement:
--   Under the original Standing Gaussian spectrally negative Levy process, its genuine q-scale W and a positive root phi, assume only that the original signed compensated generator kernel is globally absolutely product-integrable at every sufficiently high admissible Laplace weight. Then the exact full source generator residual (X.generator W-qW) is integrable and has vanishing weighted Laplace transform on some terminal half-line. The proof derives weighted W'' integrability from the original source's Gaussian analytic scale reconstruction, takes genuine Fubini and jump section integrability from the product assumption, and supplies the right-hand Gaussian slope 2/sigma squared rather than the false ordinary derivative at origin. This independent bridge will be instantiated by the separate source product theorem.
-- source:
--   Proved fixed-weight Gaussian identity and source C2, right slope, Fubini and weighted W''; Mathlib 0df444a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_weighted
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable
import Theorems.Thm_AvramDividend_Classical_avram_root29_06_gaussian_weighted_residual_three_gaps
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
/-- The true Gaussian generator residual has a vanishing weighted transform
    for all sufficiently large admissible weights. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_residual_from_eventual_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hprod : ∃ bJ : ℝ, ∀ θ : ℝ, bJ ≤ θ → 0 ≤ θ → q < X.ψ θ →
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod
          (X.ν.restrict (Iio (0 : ℝ))))) :
    ∃ b : ℝ, ∀ θ : ℝ, b ≤ θ → 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0 := by sorry
