-- Prove2me | solution 1 for isCompact_setOf_numericalRadius_sub_smul_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:49.382217+00:00
-- url     : https://prove2.me/submissions/7767c68c-d05c-4d5d-a86e-b55994447dbc

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_norm_sub_numericalRadius_le_numericalRadius_sub_smul_one
import Theorems.Thm_continuous_numericalRadius_sub_smul_one

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) (r : ℝ) :
    IsCompact {c : ℂ | numericalRadius (A - c • 1) ≤ r} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_le (continuous_numericalRadius_sub_smul_one A)
      continuous_const
  · apply (Metric.isBounded_closedBall :
      Bornology.IsBounded
        (Metric.closedBall (0 : ℂ) (r + numericalRadius A))).subset
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right]
    change numericalRadius (A - c • 1) ≤ r at hc
    have hcoercive :=
      norm_sub_numericalRadius_le_numericalRadius_sub_smul_one A c
    linarith
