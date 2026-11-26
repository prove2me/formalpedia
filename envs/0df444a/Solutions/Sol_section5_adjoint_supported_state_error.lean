-- Prove2me | solution 1 for section5_adjoint_supported_state_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:39.987084+00:00
-- url     : https://prove2.me/submissions/e45687d2-a9bd-46ab-ac8a-e1ace4a46172

import Mathlib
set_option autoImplicit false
open MeasureTheory
theorem solution
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T A S : E →L[ℂ] H) (ψ φ : H) (δ ε : ℝ)
    (hT : ‖T‖ ≤ 1) (hAS : ‖S-A‖ ≤ δ) (hψ : ‖ψ‖ ≤ 1)
    (hsupport : ContinuousLinearMap.adjoint A ψ=ContinuousLinearMap.adjoint T ψ)
    (hstates : ‖ψ-φ‖ ≤ ε) :
    ‖ContinuousLinearMap.adjoint S ψ-ContinuousLinearMap.adjoint T φ‖ ≤ δ+ε := by
  have hδ : 0 ≤ δ := (norm_nonneg (S-A)).trans hAS
  have hnorm : ‖ContinuousLinearMap.adjoint (S-A)‖ ≤ δ := by
    rwa [ContinuousLinearMap.adjoint.norm_map]
  have hnormT : ‖ContinuousLinearMap.adjoint T‖ ≤ 1 := by
    rwa [ContinuousLinearMap.adjoint.norm_map]
  have heq : ContinuousLinearMap.adjoint S ψ-ContinuousLinearMap.adjoint T φ =
      ContinuousLinearMap.adjoint (S-A) ψ+ContinuousLinearMap.adjoint T (ψ-φ) := by
    simp only [map_sub,ContinuousLinearMap.sub_apply,hsupport]
    abel
  rw [heq]
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint (S-A) ψ‖+‖ContinuousLinearMap.adjoint T (ψ-φ)‖ := norm_add_le _ _
    _ ≤ ‖ContinuousLinearMap.adjoint (S-A)‖*‖ψ‖+‖ContinuousLinearMap.adjoint T‖*‖ψ-φ‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ δ*1+1*ε := add_le_add
      (mul_le_mul hnorm hψ (norm_nonneg _) hδ)
      (mul_le_mul hnormT hstates (norm_nonneg _) (by norm_num))
    _ = _ := by ring
