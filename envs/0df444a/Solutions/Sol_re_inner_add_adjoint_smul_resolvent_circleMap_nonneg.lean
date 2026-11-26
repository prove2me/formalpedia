-- Prove2me | solution 1 for re_inner_add_adjoint_smul_resolvent_circleMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:19.805885+00:00
-- url     : https://prove2.me/submissions/cffbdcfc-5e2a-4f62-811a-1a69d0132278

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_re_inner_smul_resolvent_circleMap_nonneg
section
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private theorem re_inner_adjoint_apply_eq [CompleteSpace E] (B : E →L[ℂ] E) (x : E) :
    (⟪x, (ContinuousLinearMap.adjoint B) x⟫_ℂ).re = (⟪x, B x⟫_ℂ).re := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    (⟪B x, x⟫_ℂ).re = ((starRingEnd ℂ) ⟪B x, x⟫_ℂ).re := (Complex.conj_re _).symm
    _ = (⟪x, B x⟫_ℂ).re := by rw [inner_conj_symm]
end

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) (x : E) :
    0 ≤ (⟪x, (((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) +
      ContinuousLinearMap.adjoint
        ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))) x⟫_ℂ).re := by
  let B := (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)
  have hpos : 0 ≤ (⟪x, B x⟫_ℂ).re := re_inner_smul_resolvent_circleMap_nonneg A hW t x
  change 0 ≤ (⟪x, (B + ContinuousLinearMap.adjoint B) x⟫_ℂ).re
  rw [add_apply, inner_add_right, Complex.add_re, re_inner_adjoint_apply_eq]
  exact add_nonneg hpos hpos
