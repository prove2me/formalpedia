-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
-- name    : AvramDividend.Classical.bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:48:18.54679+00:00
-- url     : https://prove2.me/theorems/711ca87b-8d2d-406a-974a-f90a8979bc32
-- title:
--   Unconditional BV q-scale generator harmonicity at every positive reserve
-- statement:
--   For any standing bounded-variation spectrally negative Lévy process and any positive q-scale function, the generator is integrable and equals q times the scale function at every strictly positive real surplus. Combine accepted BV C1 regularity, generator continuity and integrability, full residual Laplace vanishing, and interval uniqueness.
-- source:
--   Avram, Palmowski and Pistorius (2007), generator harmonicity; Prove2Me verified theorems f9004ff3, bae40e79, 8709592d, d42981f3 and 19029a99.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
import Mathlib.Tactic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by sorry
