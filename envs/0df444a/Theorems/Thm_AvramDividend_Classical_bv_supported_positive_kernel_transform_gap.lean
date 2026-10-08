-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_supported_positive_kernel_transform_gap
-- name    : AvramDividend.Classical.bv_supported_positive_kernel_transform_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:37:36.535828+00:00
-- url     : https://prove2.me/theorems/53172041-5bc2-4a46-99fe-0132e91bced4
-- title:
--   The bounded-variation renewal kernel is supported on nonnegative reserves and has a contractive Laplace parameter
-- statement:
--   Strengthen the proved bounded-variation positive-kernel construction by certifying that the constructed kernel is supported on nonnegative reserve levels. Retain the full shifted Laplace transform formula at all positive discounts, local s-finiteness and one strict contraction parameter. The support condition is essential for Laplace monotonicity, for supporting convolution powers, and for the cumulative-renewal measure identity.
-- source:
--   The published Proved bv_positive_kernel_transform_gap (f08a7618), positiveLaplace_tilted_kernel_measure (9fc5f28e), bv_jump_magnitude_sfinite (8f6d4571), with the generic published pending positive_halfline_withDensity_sum_supported support lemma. Avram/Palmowski/Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_supported_positive_kernel_transform_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ κ : Measure ℝ,
      SFinite κ ∧ κ (Iio (0 : ℝ)) = 0 ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) =
          ∫⁻ z : ℝ≥0, ENNReal.ofReal
            ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) ∧
      (∃ s : ℝ, 0 < s ∧
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) <
          ENNReal.ofReal X.drift) := by sorry
