-- Prove2me | solution 1 for polynomialSupNorm_mul_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:55.828584+00:00
-- url     : https://prove2.me/submissions/12373437-2e93-44f0-be23-e179c24e7b72

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open scoped InnerProductSpace
theorem _root_.solution
    {S : Set ℂ} (hS : IsCompact S) (p q : Polynomial ℂ) :
    polynomialSupNorm (p * q) S ≤
      polynomialSupNorm p S * polynomialSupNorm q S := by
  unfold polynomialSupNorm
  apply ciSup_le
  intro z
  by_cases hz : z ∈ S
  · have : Nonempty (z ∈ S) := ⟨hz⟩
    apply ciSup_le
    intro hz'
    rw [Polynomial.eval_mul, norm_mul]
    exact mul_le_mul
      (norm_eval_le_polynomialSupNorm p
        (bddAbove_norm_eval_image_of_isCompact p hS) hz')
      (norm_eval_le_polynomialSupNorm q
        (bddAbove_norm_eval_image_of_isCompact q hS) hz')
      (norm_nonneg _) (polynomialSupNorm_nonneg p S)
  · have : IsEmpty (z ∈ S) := ⟨fun h ↦ hz h⟩
    rw [iSup_of_empty', Real.sSup_empty]
    exact mul_nonneg (polynomialSupNorm_nonneg p S)
      (polynomialSupNorm_nonneg q S)
