-- Prove2me | solution 1 for re_inner_add_adjoint_smul_resolvent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:31.83295+00:00
-- url     : https://prove2.me/submissions/3edfe3d1-2069-450b-b5fa-7ee1af7a2938

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_re_inner_smul_resolvent_nonneg
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
    (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) (x : E) :
    0 ≤ (⟪x, ((ν • resolvent A σ) +
      ContinuousLinearMap.adjoint (ν • resolvent A σ)) x⟫_ℂ).re := by
  let B := ν • resolvent A σ
  have hpos : 0 ≤ (⟪x, B x⟫_ℂ).re := re_inner_smul_resolvent_nonneg A hW x
  change 0 ≤ (⟪x, (B + ContinuousLinearMap.adjoint B) x⟫_ℂ).re
  rw [add_apply, inner_add_right, Complex.add_re, re_inner_adjoint_apply_eq]
  exact add_nonneg hpos hpos
