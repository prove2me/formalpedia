-- Prove2me | solution 1 for convex_centeredNumericalRadiusMinimizers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:20.148474+00:00
-- url     : https://prove2.me/submissions/629931e1-e879-46df-ae60-b9885db7ef10

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_convex_setOf_numericalRadius_sub_smul_one_le
import Theorems.Thm_exists_center_minimizing_numericalRadius
import Theorems.Thm_centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution (A : E →L[ℂ] E) :
    Convex ℝ (centeredNumericalRadiusMinimizers A) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  rw [centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer A hc]
  exact convex_setOf_numericalRadius_sub_smul_one_le A
    (numericalRadius (A - c • 1))
