-- Prove2me | solution 1 for norm_sub_numericalRadius_le_numericalRadius_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:39.927196+00:00
-- url     : https://prove2.me/submissions/ac1e9370-56ae-47dc-b3f1-bdaf653903ba

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖c‖ - numericalRadius A ≤ numericalRadius (A - c • 1) := by
  have h :=
    abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius A c
  rw [abs_le] at h
  linarith
