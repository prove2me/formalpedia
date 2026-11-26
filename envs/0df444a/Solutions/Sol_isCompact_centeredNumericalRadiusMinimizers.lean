-- Prove2me | solution 1 for isCompact_centeredNumericalRadiusMinimizers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:38:05.410106+00:00
-- url     : https://prove2.me/submissions/58ace49f-01fa-445c-b906-b2ba7d010813

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_isCompact_setOf_numericalRadius_sub_smul_one_le
import Theorems.Thm_exists_center_minimizing_numericalRadius
import Theorems.Thm_centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution (A : E →L[ℂ] E) :
    IsCompact (centeredNumericalRadiusMinimizers A) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  rw [centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer A hc]
  exact isCompact_setOf_numericalRadius_sub_smul_one_le A
    (numericalRadius (A - c • 1))
