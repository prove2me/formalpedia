-- Prove2me | solution 1 for numericalRadius_adjoint_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:44:44.690075+00:00
-- url     : https://prove2.me/submissions/c34216db-65a7-443c-ba0b-756931c64dc8

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_Compression
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRadius_nonneg
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg



set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem _root_.solution
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) :
    numericalRadius ((V† ∘L A) ∘L V) ≤ ‖V‖ ^ 2 * numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_)
    (mul_nonneg (sq_nonneg ‖V‖) (numericalRadius_nonneg A))
  refine Real.iSup_le (fun hz => ?_)
    (mul_nonneg (sq_nonneg ‖V‖) (numericalRadius_nonneg A))
  obtain ⟨x, hx, rfl⟩ :=
    (mem_numericalRange ((V† ∘L A) ∘L V) z).mp hz
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_inner_right]
  calc
    ‖⟪V x, A (V x)⟫_ℂ‖ ≤ numericalRadius A * ‖V x‖ ^ 2 :=
      norm_inner_apply_self_le_numericalRadius_mul_norm_sq A (V x)
    _ ≤ numericalRadius A * (‖V‖ * ‖x‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg (V x)) (V.le_opNorm x) 2)
        (numericalRadius_nonneg A)
    _ = ‖V‖ ^ 2 * numericalRadius A := by rw [hx]; ring
