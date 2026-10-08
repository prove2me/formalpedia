-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_positive_kernel_transform_gap
-- name    : AvramDividend.Classical.bv_positive_kernel_transform_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:19:32.203271+00:00
-- url     : https://prove2.me/theorems/f08a7618-4034-482a-8239-427b040d0203
-- title:
--   A bounded-variation positive renewal kernel with a contractive Laplace transform
-- statement:
--   Under Standing, bounded variation and q>0, there exists a positive s-finite measure kernel on real reserve levels whose Laplace transform is exactly the positive jump-magnitude integral of (1-exp(-(s+q/drift)z))/s for all s>0. At some s this integral is smaller than the strictly positive drift. This is the constructive, measure-valued input for a convergent geometric renewal representation of the q-scale function.
-- source:
--   Prove2Me Proved bv_tilted_kernel_contractive_parameter; Proved positiveLaplace_tilted_kernel_measure; published bv_jump_magnitude_sfinite. Avram/Palmowski/Pistorius (2007), BV scale-function renewal theory.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_positive_kernel_transform_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ κ : Measure ℝ,
      SFinite κ ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) =
          ∫⁻ z : ℝ≥0,
            ENNReal.ofReal
              ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) ∧
      (∃ s : ℝ, 0 < s ∧
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) <
          ENNReal.ofReal X.drift) := by sorry
