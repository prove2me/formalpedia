-- Prove2me | solution 1 for exists_imaginary_mem_centeredNumericalRadiusMinimizers_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:43:07.384953+00:00
-- url     : https://prove2.me/submissions/1558aa65-cf99-4664-bfd8-3ceaaa117ebe

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers
import Theorems.Thm_exists_imaginary_mem_centeredNumericalRadiusMinimizers

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ,
      (r : ℂ) * Complex.I ∈ centeredNumericalRadiusMinimizers A ∧
        ‖(r : ℂ) * Complex.I‖ ≤ 2 * numericalRadius A := by
  obtain ⟨r, hr⟩ := exists_imaginary_mem_centeredNumericalRadiusMinimizers A hA
  exact ⟨r, hr,
    norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hr⟩
