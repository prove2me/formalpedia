-- Prove2me | solution 1 for inverseCayley_cayleyTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:33.004123+00:00
-- url     : https://prove2.me/submissions/99507706-3bdc-41c2-941d-7c9efadd0f1e

import Definitions.Def_Spectral_Cayley_Unitary
import Definitions.Def_Spectral_Cayley_Inverse
import Theorems.Thm_add_I_surjective_of_isSelfAdjoint
import Theorems.Thm_cayleyTransform_apply_plus
import Theorems.Thm_cayleyTransform_unitary
import Theorems.Thm_dense_range_one_sub_cayleyTransform
import Theorems.Thm_one_not_mem_eigenvalues_cayleyTransform

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem oneSub_cayley_apply_plus
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (x : A.domain) :
    oneSub (cayleyTransform A hA) (A x + Complex.I • (x : E)) =
      ((2 : ℂ) * Complex.I) • (x : E) := by
  change (A x + Complex.I • (x : E)) -
    cayleyTransform A hA (A x + Complex.I • (x : E)) = _
  rw [cayleyTransform_apply_plus A hA x]
  module
private theorem range_oneSub_cayley_eq_domain
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    LinearMap.range (oneSub (cayleyTransform A hA)) = A.domain := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hy
    obtain ⟨x, hx⟩ := add_I_surjective_of_isSelfAdjoint A hA z
    change A x + Complex.I • (x : E) = z at hx
    have hyEq : y = ((2 : ℂ) * Complex.I) • (x : E) := by
      rw [← hz, ← hx]
      exact oneSub_cayley_apply_plus A hA x
    rw [hyEq]
    exact A.domain.smul_mem ((2 : ℂ) * Complex.I) x.property
  · intro y hy
    let x : A.domain := ⟨y, hy⟩
    have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by norm_num) Complex.I_ne_zero
    refine LinearMap.mem_range.mpr
      ⟨(((2 : ℂ) * Complex.I)⁻¹) • (A x + Complex.I • (x : E)), ?_⟩
    rw [map_smul, oneSub_cayley_apply_plus A hA x, smul_smul,
      inv_mul_cancel₀ htwoI, one_smul]
end

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    inverseCayley (cayleyTransform A hA) (cayleyTransform_unitary A hA)
      (one_not_mem_eigenvalues_cayleyTransform A hA)
      (dense_range_one_sub_cayleyTransform A hA) = A := by
  apply LinearPMap.dExt (range_oneSub_cayley_eq_domain A hA)
  intro x y hxy
  let U := cayleyTransform A hA
  let L := oneSub U
  let e : E ≃ₗ[ℂ] LinearMap.range L :=
    LinearEquiv.ofInjective L
      (oneSub_injective U (one_not_mem_eigenvalues_cayleyTransform A hA))
  let z : E := (((2 : ℂ) * Complex.I)⁻¹) • (A y + Complex.I • (y : E))
  have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hLz : L z = (y : E) := by
    change oneSub U z = (y : E)
    change oneSub U
      ((((2 : ℂ) * Complex.I)⁻¹) • (A y + Complex.I • (y : E))) = (y : E)
    rw [map_smul, oneSub_cayley_apply_plus A hA y, smul_smul,
      inv_mul_cancel₀ htwoI, one_smul]
  have hez : e.symm x = z := by
    apply oneSub_injective U (one_not_mem_eigenvalues_cayleyTransform A hA)
    change L (e.symm x) = L z
    rw [hLz]
    have heapply := congrArg Subtype.val (e.apply_symm_apply x)
    change L (e.symm x) = (x : E) at heapply
    exact heapply.trans hxy
  change Complex.I • oneAdd U (e.symm x) = A y
  rw [hez]
  change Complex.I • (z + U z) = A y
  change Complex.I •
    (((2 * Complex.I)⁻¹ : ℂ) • (A y + Complex.I • (y : E)) +
      U (((2 * Complex.I)⁻¹ : ℂ) • (A y + Complex.I • (y : E)))) = A y
  rw [map_smul, cayleyTransform_apply_plus A hA y, ← smul_add]
  have hsum : (A y + Complex.I • (y : E)) + (A y - Complex.I • (y : E)) =
      (2 : ℂ) • A y := by
    module
  rw [hsum, smul_smul, smul_smul]
  have hc : Complex.I * ((2 * Complex.I)⁻¹ : ℂ) * 2 = 1 := by
    calc
      Complex.I * ((2 * Complex.I)⁻¹ : ℂ) * 2 =
          ((2 * Complex.I)⁻¹ : ℂ) * (2 * Complex.I) := by ring
      _ = 1 := inv_mul_cancel₀ htwoI
  rw [hc, one_smul]
