-- Prove2me | solution 1 for isPositive_add_adjoint_smul_resolvent_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:08.047647+00:00
-- url     : https://prove2.me/submissions/fb8af827-f612-4f08-90aa-502a22b3d087

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_re_inner_add_adjoint_smul_resolvent_circleMap_nonneg

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) :
    ContinuousLinearMap.IsPositive
      (((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) +
        ContinuousLinearMap.adjoint
          ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact IsSelfAdjoint.add_star_self _
  · intro x
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [inner_re_symm]
    exact re_inner_add_adjoint_smul_resolvent_circleMap_nonneg A hW t x
