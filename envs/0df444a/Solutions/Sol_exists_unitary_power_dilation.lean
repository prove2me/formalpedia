-- Prove2me | solution 1 for exists_unitary_power_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:43:52.877437+00:00
-- url     : https://prove2.me/submissions/247dab53-e7cc-437f-ad52-aac1a150ff17

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Operator_Dilation_Halmos
import Definitions.Def_Operator_Dilation_Schaeffer
import Theorems.Thm_inner_schaefferNetworkEmbedding
import Theorems.Thm_adjoint_schaefferNetworkEmbedding_apply
import Theorems.Thm_exists_halmos_unitary_dilation

section
open scoped ENNReal InnerProductSpace
universe u
noncomputable section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem schaefferGlobalOperator_mem_unitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    schaefferGlobalOperator J ∈
      unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  (schaefferGlobalUnitary J).property
@[simp]
private theorem schaefferGlobalOperator_apply
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferGlobalOperator J f i = WithLp.toLp 2
      (((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E) (f i)).fst,
        ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
          (f (schaefferIntShift.symm i))).snd) := by
  change schaefferRouteEquiv
    (lpPointwiseEquiv (Unitary.linearIsometryEquiv J) f) i = _
  rfl
@[simp]
private theorem schaefferOrbit_succ_apply
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (n : ℕ) (x : E) (i : ℤ) :
    schaefferOrbit J (n + 1) x i = WithLp.toLp 2
      (((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (schaefferOrbit J n x i)).fst,
       ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (schaefferOrbit J n x (schaefferIntShift.symm i))).snd) := by
  rw [schaefferOrbit, pow_succ']
  exact schaefferGlobalOperator_apply J _ i
private theorem schaeffer_power_state
    (T : E →L[ℂ] E)
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (hJ : ∀ z : E,
      ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (WithLp.toLp 2 (z, 0))).fst = T z)
    (n : ℕ) (x : E) :
    (schaefferOrbit J n x 0).fst = (T ^ n) x ∧
    (schaefferOrbit J n x 0).snd = 0 ∧
    ∀ i : ℤ, i < 0 → schaefferOrbit J n x i = 0 := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
          schaefferNetworkEmbedding_apply, lp.single_apply_self,
          WithLp.toLp_fst]
      · simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
          schaefferNetworkEmbedding_apply, lp.single_apply_self,
          WithLp.toLp_snd]
      intro i hi
      simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
        schaefferNetworkEmbedding_apply]
      rw [lp.single_apply_ne]
      exact ne_of_lt hi
  | succ n ih =>
      rcases ih with ⟨ihfst, ihsnd, ihneg⟩
      have hzero : schaefferOrbit J n x 0 = WithLp.toLp 2 ((T ^ n) x, 0) := by
        apply WithLp.ofLp_injective
        exact Prod.ext ihfst ihsnd
      refine ⟨?_, ?_, ?_⟩
      · rw [schaefferOrbit_succ_apply, WithLp.toLp_fst, hzero, hJ,
          pow_succ', mul_apply_eq_comp]
      · rw [schaefferOrbit_succ_apply, WithLp.toLp_snd]
        have hm1 : schaefferIntShift.symm (0 : ℤ) = -1 := rfl
        rw [hm1, ihneg (-1) (by omega), map_zero]
        rfl
      · intro i hi
        rw [schaefferOrbit_succ_apply]
        have hprev : schaefferIntShift.symm i < 0 := by
          change i - 1 < 0
          omega
        rw [ihneg i hi, ihneg _ hprev, map_zero]
        rfl
end
end

set_option autoImplicit false
open scoped ENNReal InnerProductSpace
universe u
noncomputable section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) := by
  obtain ⟨J, hJunitary, hJcompression⟩ := exists_halmos_unitary_dilation T hT
  let JU : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E) :=
    ⟨J, hJunitary⟩
  have hJU : ∀ z : E,
      ((JU : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (WithLp.toLp 2 (z, 0))).fst = T z := hJcompression
  refine ⟨SchaefferNetworkSpace E, inferInstance, inferInstance, inferInstance,
    schaefferNetworkEmbedding, schaefferGlobalOperator JU, ?_, ?_, ?_⟩
  · exact inner_schaefferNetworkEmbedding
  · exact schaefferGlobalOperator_mem_unitary JU
  · intro n x
    rw [adjoint_schaefferNetworkEmbedding_apply]
    change (schaefferOrbit JU n x 0).fst = (T ^ n) x
    exact (schaeffer_power_state T JU hJU n x).1
