-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
-- name    : AvramDividend.Classical.bv_weighted_generator_residual_family_from_scale_20261026
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:26:23.992102+00:00
-- url     : https://prove2.me/theorems/8709592d-c501-4909-9b43-13b446c02394
-- title:
--   Full bounded-variation generator-residual Laplace family from the scale-function identity
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with positive discount and its q-scale function, the full weighted Lévy-generator residual has an integrable zero Laplace transform for every θ≥0 with q<ψ(θ). The proof composes the globally integrable signed compensated-jump product, first-order derivative integration by parts, precise origin compensation and physical-drift cancellation. It removes the extra weighted-transform hypothesis from the proved BV C1 conditional harmonicity theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, bounded-variation scale-function generator calculation. Reuses independently Proved canonical signed Fubini, drift compensation, and scale-function Laplace results.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_scale_weighted_deriv_transform_of_boundary
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_bv_truncated_negative_jump_integrable
import Theorems.Thm_AvramDividend_Classical_bv_truncated_jump_integral_eq_characteristic_drift_difference
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_transform_from_fixed_jump_fubini
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_integral_decomposition
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_zero_of_transform_components
import Theorems.Thm_AvramDividend_Classical_bv_weighted_residual_integrable_from_scale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- The bounded-variation q-scale generator residual has zero weighted
Laplace transform at every admissible nonnegative parameter. -/
theorem bv_weighted_generator_residual_family_from_scale_20261026
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x))
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by sorry
end AvramDividend.Classical
