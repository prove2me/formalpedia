-- Prove2me | solution 1 for isPositive_add_adjoint_smul_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:08.998686+00:00
-- url     : https://prove2.me/submissions/f166183b-3977-4735-b945-3de6b3553d95

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_re_inner_add_adjoint_smul_resolvent_nonneg

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) :
    ContinuousLinearMap.IsPositive ((ν • resolvent A σ) +
      ContinuousLinearMap.adjoint (ν • resolvent A σ)) := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact IsSelfAdjoint.add_star_self _
  · intro x
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [inner_re_symm]
    exact re_inner_add_adjoint_smul_resolvent_nonneg A hW x
