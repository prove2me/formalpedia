-- Prove2me | solution 1 for numericalRadius_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:35.930819+00:00
-- url     : https://prove2.me/submissions/e4d440fc-727c-4827-849e-bd4aeffff2ec

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_numericalRadius
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_le_norm
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_adjoint
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero



set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution :
    numericalRadius (1 : E →L[ℂ] E) = 1 := by
  apply le_antisymm
  · simpa only [norm_one] using
      numericalRadius_le_norm (1 : E →L[ℂ] E)
  · have hmem : (1 : ℂ) ∈ numericalRange (1 : E →L[ℂ] E) := by
      rw [show (1 : E →L[ℂ] E) = (1 : ℂ) • 1 by simp,
        numericalRange_scalar]
      exact Set.mem_singleton 1
    simpa only [norm_one] using
      norm_le_numericalRadius (1 : E →L[ℂ] E) hmem
