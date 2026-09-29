-- Prove2me | solution 1 for mme_MMObj_permObj_swapFirstTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:37:49.084724+00:00
-- url     : https://prove2.me/submissions/4ba42dfe-de94-4913-b910-e1ac58c6bfd2

import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value

open PiTensorProduct BigOperators
open MME

universe u v w

set_option autoImplicit false
set_option warningAsError true

namespace MME.MMObjSwapFirstTwo

noncomputable def transposeLinear
    {K : Type u} [Field K] (α : Type v) (β : Type w) :
    (α × β → K) →ₗ[K] (β × α → K) where
  toFun f p := f (p.2, p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem transposeLinear_single
    {K : Type u} [Field K] {α : Type v} {β : Type w}
    [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    transposeLinear (K := K) α β (Pi.single (a, b) 1) =
      Pi.single (b, a) 1 := by
  ext p
  by_cases h : p = (b, a)
  · subst p
    simp [transposeLinear]
  · have h' : (p.2, p.1) ≠ (a, b) := by
      intro hp
      apply h
      cases p
      simp_all
    simp [transposeLinear, h, h']

end MME.MMObjSwapFirstTwo

/-- Swapping the first two tensor modes reverses the outside dimensions of a
matrix-multiplication tensor. -/
theorem solution
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p))
      (MMObj K p m n) := by
  let fwd : ∀ s : Fin 3,
      (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p)).V s →ₗ[K]
        (MMObj K p m n).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ =>
        exact MME.MMObjSwapFirstTwo.transposeLinear (K := K) (Fin m) (Fin p)
    | 1, _ =>
        exact MME.MMObjSwapFirstTwo.transposeLinear (K := K) (Fin n) (Fin m)
    | 2, _ =>
        exact MME.MMObjSwapFirstTwo.transposeLinear (K := K) (Fin p) (Fin n)
    | s + 3, h => exact absurd h (by omega)
  let bwd : ∀ s : Fin 3,
      (MMObj K p m n).V s →ₗ[K]
        (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p)).V s :=
    fun ⟨s, hs⟩ => by
      match s, hs with
      | 0, _ =>
          exact MME.MMObjSwapFirstTwo.transposeLinear (K := K) (Fin p) (Fin m)
      | 1, _ =>
          exact MME.MMObjSwapFirstTwo.transposeLinear (K := K) (Fin m) (Fin n)
      | 2, _ =>
          exact MME.MMObjSwapFirstTwo.transposeLinear (K := K) (Fin n) (Fin p)
      | s + 3, h => exact absurd h (by omega)
  have hcomp :
      (fun s => fwd s ∘ₗ bwd s) =
        fun s => (LinearMap.id : (MMObj K p m n).V s →ₗ[K] _) := by
    funext ⟨s, hs⟩
    match s, hs with
    | 0, _ =>
        apply LinearMap.ext
        intro f
        funext x
        rfl
    | 1, _ =>
        apply LinearMap.ext
        intro f
        funext x
        rfl
    | 2, _ =>
        apply LinearMap.ext
        intro f
        funext x
        rfl
    | s + 3, h => exact absurd h (by omega)
  have hbwd_t :
      PiTensorProduct.map bwd (MMTensor K p m n) =
        (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p)).t := by
    show PiTensorProduct.map bwd
        (∑ i : Fin p, ∑ j : Fin m, ∑ k : Fin n,
          tprod K (fun s => match s with
            | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin p × Fin m → K)
            | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin n → K)
            | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin n × Fin p → K))) =
        (PiTensorProduct.reindex K (MMSpace K n m p) swapFirstTwoPerm)
          (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
            tprod K (fun s => match s with
              | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
              | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
              | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K)))
    simp only [map_sum, PiTensorProduct.map_tprod,
      PiTensorProduct.reindex_tprod]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, j]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ext ⟨s, hs⟩
    match s, hs with
    | 0, _ =>
        exact
          (MME.MMObjSwapFirstTwo.transposeLinear_single
            (K := K) k j)
    | 1, _ =>
        exact
          (MME.MMObjSwapFirstTwo.transposeLinear_single
            (K := K) j i)
    | 2, _ =>
        exact
          (MME.MMObjSwapFirstTwo.transposeLinear_single
            (K := K) i k)
    | s + 3, h => exact absurd h (by omega)
  have hbwd :
      TensorObj.Restrict
        (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p))
        (MMObj K p m n) := ⟨bwd, hbwd_t⟩
  have hfwd :
      TensorObj.Restrict (MMObj K p m n)
        (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p)) := by
    refine ⟨fwd, ?_⟩
    rw [← hbwd_t]
    have hmc :
        PiTensorProduct.map (fun s => fwd s ∘ₗ bwd s) =
          (PiTensorProduct.map fwd).comp (PiTensorProduct.map bwd) :=
      PiTensorProduct.map_comp _ _
    have h1 := congrFun (congrArg DFunLike.coe hmc) (MMTensor K p m n)
    rw [hcomp] at h1
    exact h1.symm.trans
      (congrFun (congrArg DFunLike.coe PiTensorProduct.map_id) _)
  exact ⟨hbwd, hfwd⟩
