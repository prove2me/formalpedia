-- Prove2me | solution 1 for exists_real_mem_centeredNumericalRadiusMinimizers_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:57.374779+00:00
-- url     : https://prove2.me/submissions/4bedc509-36e8-4a16-9868-9484591157fa

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers
import Theorems.Thm_exists_real_mem_centeredNumericalRadiusMinimizers

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, (r : ℂ) ∈ centeredNumericalRadiusMinimizers A ∧
      ‖(r : ℂ)‖ ≤ 2 * numericalRadius A := by
  obtain ⟨r, hr⟩ := exists_real_mem_centeredNumericalRadiusMinimizers A hA
  exact ⟨r, hr,
    norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hr⟩
