-- Prove2me | solution 1 for exteriorPower.iotaMulti_comp_eq_det_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5456a955-d4d7-58f6-b71e-ad341a083770

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exteriorPower_iotaMulti_comp_eq_det_smul

set_option autoImplicit false

namespace ExteriorPowerDet

lemma alternatingMap_apply_matrix_smul {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] {n : ℕ} (g : M [⋀^Fin n]→ₗ[A] N) (f : Fin n → M)
    (a : Matrix (Fin n) (Fin n) A) :
    g (fun j => ∑ i, a i j • f i) = a.det • g f := by
  classical
  let L : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A f
  let b : Module.Basis (Fin n) A (Fin n → A) := Pi.basisFun A (Fin n)
  have hL : ∀ i, L (b i) = f i := fun i => by
    simp [L, b, Fintype.linearCombination_apply_single]
  have key : g.compLinearMap L = b.det.smulRight (g f) := by
    refine Module.Basis.ext_alternating b fun v hv => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have h1 : (fun i => L (b (v i))) = f ∘ σ := funext fun i => hL (v i)
    have h2 : (fun i => b (v i)) = b ∘ σ := rfl
    rw [AlternatingMap.compLinearMap_apply, h1, AlternatingMap.map_perm, AlternatingMap.smulRight_apply,
      h2, AlternatingMap.map_perm, Module.Basis.det_self]
    simp [Units.smul_def, Int.cast_smul_eq_zsmul]
  have h3 : (fun j => ∑ i, a i j • f i) = fun j => L (a.transpose j) := by
    funext j
    simp [L, Fintype.linearCombination_apply, Matrix.transpose_apply]
  have h4 := congrArg (fun G : (Fin n → A) [⋀^Fin n]→ₗ[A] N => G (fun j => a.transpose j)) key
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smulRight_apply] at h4
  rw [h3, h4, show (fun j => a.transpose j) = a.transpose from rfl, Pi.basisFun_det_apply]
  congr 1
  exact Matrix.det_transpose a

lemma ιMulti_matrix_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {n : ℕ} (f : Fin n → M) (a : Matrix (Fin n) (Fin n) A) :
    exteriorPower.ιMulti A n (fun j => ∑ i, a i j • f i) = a.det • exteriorPower.ιMulti A n f :=
  alternatingMap_apply_matrix_smul (exteriorPower.ιMulti A n) f a

end ExteriorPowerDet

open ExteriorPowerDet in
theorem solution {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) (f : M →ₗ[A] M) (m : Fin n → M) :
    exteriorPower.ιMulti A n (f ∘ m) = LinearMap.det f • exteriorPower.ιMulti A n m := by
  classical

  let c : Matrix (Fin n) (Fin n) A := fun i j => b.repr (m j) i
  let T : Matrix (Fin n) (Fin n) A := LinearMap.toMatrix b b f
  have hm : (fun j => ∑ i, c i j • b i) = m := by
    funext j
    exact b.sum_repr (m j)
  have hfb : ∀ i, f (b i) = ∑ k, T k i • b k := by
    intro i
    have h := b.sum_repr (f (b i))
    simp only [T, LinearMap.toMatrix_apply]
    exact h.symm
  have hfm : (fun j => ∑ k, (T * c) k j • b k) = f ∘ m := by
    funext j
    have h1 : f (m j) = ∑ i, c i j • f (b i) := by
      have := congrArg f (congrFun hm j)
      rw [map_sum] at this
      simpa only [map_smul] using this.symm
    rw [Function.comp_apply, h1]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfb i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm]
  rw [← hfm, ιMulti_matrix_smul, Matrix.det_mul, ← hm, ιMulti_matrix_smul, smul_smul]
  simp only [T, LinearMap.det_toMatrix]

end S_exteriorPower_iotaMulti_comp_eq_det_smul
end P2MW
export P2MW.S_exteriorPower_iotaMulti_comp_eq_det_smul (solution)
