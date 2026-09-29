-- Prove2me | solution 1 for mme_CW_coupled_low_block_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:56:54.557634+00:00
-- url     : https://prove2.me/submissions/477440a3-5902-4ff9-b59d-4c4b112a1712

import Definitions.Def_mme_CW_coupled_value

open MME PiTensorProduct BigOperators

universe u

namespace CWCoupledLowBlockRestrict

noncomputable def xMap {K : Type u} [Field K] (q : ℕ) :
    (CoupledSpace K q 0) →ₗ[K] (MMObj K 1 q 1).V 0 where
  toFun v ij := v (Sum.inl ij.2)
  map_add' x y := rfl
  map_smul' c x := rfl

noncomputable def yMap {K : Type u} [Field K] (q : ℕ) :
    (CoupledSpace K q 1) →ₗ[K] (MMObj K 1 q 1).V 1 where
  toFun v jk := v (Sum.inl jk.1)
  map_add' x y := rfl
  map_smul' c x := rfl

noncomputable def zMap {K : Type u} [Field K] (q : ℕ) :
    (CoupledSpace K q 2) →ₗ[K] (MMObj K 1 q 1).V 2 where
  toFun v _ := v (Sum.inl 0)
  map_add' x y := rfl
  map_smul' c x := rfl

noncomputable def maps {K : Type u} [Field K] (q : ℕ) :
    ∀ s : Fin 3, (coupledObj K q).V s →ₗ[K] (MMObj K 1 q 1).V s
  | ⟨0, _⟩ => xMap q
  | ⟨1, _⟩ => yMap q
  | ⟨2, _⟩ => zMap q
  | ⟨n + 3, h⟩ => absurd h (by omega)

theorem selected_tensor {K : Type u} [Field K] (q : ℕ) :
    PiTensorProduct.map (maps q) (coupledObj K q).t = (MMObj K 1 q 1).t := by
  change PiTensorProduct.map (maps q) (coupledTensor K q) = MMTensor K 1 q 1
  change PiTensorProduct.map (maps q)
      ((∑ i : Fin q, tprod K (fun s =>
          match s with
          | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨2, _⟩ => (Pi.single (Sum.inl (0 : Fin 2)) 1 :
              (Fin 2 ⊕ (Fin q × Fin q)) → K))) +
       (∑ k : Fin q, tprod K (fun s =>
          match s with
          | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨2, _⟩ => (Pi.single (Sum.inl (1 : Fin 2)) 1 :
              (Fin 2 ⊕ (Fin q × Fin q)) → K))) +
       (∑ i : Fin q, ∑ k : Fin q, tprod K (fun s =>
          match s with
          | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
              (Fin 2 ⊕ (Fin q × Fin q)) → K))) +
       (∑ i : Fin q, ∑ k : Fin q, tprod K (fun s =>
          match s with
          | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
          | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
              (Fin 2 ⊕ (Fin q × Fin q)) → K)))) =
      MMTensor K 1 q 1
  unfold MMTensor
  simp only [map_add, map_sum, PiTensorProduct.map_tprod]
  simp only [Fin.sum_univ_one]
  have hB (k : Fin q) :
      tprod K (fun s => (maps q s)
        (match s with
        | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨2, _⟩ => (Pi.single (Sum.inl (1 : Fin 2)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K))) = 0 := by
    apply MultilinearMap.map_coord_zero (tprod K) (0 : Fin 3)
    apply funext
    intro ij
    change (Pi.single (Sum.inr k) (1 : K) : (Fin q ⊕ Fin q) → K)
      (Sum.inl ij.2) = 0
    exact Pi.single_eq_of_ne (by simp) 1
  have hC (i k : Fin q) :
      tprod K (fun s => (maps q s)
        (match s with
        | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K))) = 0 := by
    apply MultilinearMap.map_coord_zero (tprod K) (1 : Fin 3)
    apply funext
    intro jk
    change (Pi.single (Sum.inr k) (1 : K) : (Fin q ⊕ Fin q) → K)
      (Sum.inl jk.1) = 0
    exact Pi.single_eq_of_ne (by simp) 1
  have hD (i k : Fin q) :
      tprod K (fun s => (maps q s)
        (match s with
        | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K))) = 0 := by
    apply MultilinearMap.map_coord_zero (tprod K) (0 : Fin 3)
    apply funext
    intro ij
    change (Pi.single (Sum.inr k) (1 : K) : (Fin q ⊕ Fin q) → K)
      (Sum.inl ij.2) = 0
    exact Pi.single_eq_of_ne (by simp) 1
  have hA (i : Fin q) :
      tprod K (fun s => (maps q s)
        (match s with
        | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        | ⟨2, _⟩ => (Pi.single (Sum.inl (0 : Fin 2)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K))) =
      tprod K (fun s =>
        match s with
        | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), i) 1 : Fin 1 × Fin q → K)
        | ⟨1, _⟩ => (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 :
            Fin 1 × Fin 1 → K)) := by
    congr 1
    funext s
    fin_cases s
    · apply funext
      rintro ⟨j, ii⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (Pi.single (Sum.inl i) (1 : K) : (Fin q ⊕ Fin q) → K)
          (Sum.inl ii) =
        (Pi.single ((0 : Fin 1), i) (1 : K) : Fin 1 × Fin q → K) (0, ii)
      simp [Pi.single_apply]
    · apply funext
      rintro ⟨ii, j⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (Pi.single (Sum.inl i) (1 : K) : (Fin q ⊕ Fin q) → K)
          (Sum.inl ii) =
        (Pi.single (i, (0 : Fin 1)) (1 : K) : Fin q × Fin 1 → K) (ii, 0)
      simp [Pi.single_apply]
    · apply funext
      rintro ⟨j, j'⟩
      have hj : j = 0 := Subsingleton.elim _ _
      have hj' : j' = 0 := Subsingleton.elim _ _
      subst j
      subst j'
      change (Pi.single (Sum.inl (0 : Fin 2)) (1 : K) :
          (Fin 2 ⊕ (Fin q × Fin q)) → K) (Sum.inl 0) =
        (Pi.single ((0 : Fin 1), (0 : Fin 1)) (1 : K) :
          Fin 1 × Fin 1 → K) (0, 0)
      simp
  simp_rw [hA, hB, hC, hD]
  simp only [Finset.sum_const_zero, add_zero, zero_add]
  rfl

end CWCoupledLowBlockRestrict

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 q 1) (coupledObj K q) := by
  exact ⟨CWCoupledLowBlockRestrict.maps q,
    CWCoupledLowBlockRestrict.selected_tensor q⟩
