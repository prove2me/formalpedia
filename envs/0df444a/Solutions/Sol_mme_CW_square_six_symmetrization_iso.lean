-- Prove2me | solution 1 for mme_CW_square_six_symmetrization_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T09:42:51.158107+00:00
-- url     : https://prove2.me/submissions/5b1f9861-1efb-4c18-bc0e-498d373754fe

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open PiTensorProduct BigOperators

namespace MME

universe u

private theorem fin_one_add_eq_add_one (q : ℕ) (i : Fin q) :
    (⟨1 + i.val, by omega⟩ : Fin (q + 2)) =
      ⟨i.val + 1, by omega⟩ := by
  apply Fin.ext
  simp [Nat.add_comm]

private theorem fin_one_add_top_eq (q : ℕ) :
    (⟨1 + q, by omega⟩ : Fin (q + 2)) =
      ⟨q + 1, by omega⟩ := by
  apply Fin.ext
  simp [Nat.add_comm]

private noncomputable def cwCyclicToBase
    (K : Type u) [Field K] (q : ℕ) :
    ∀ s : Fin 3,
      CWSpace K q (cyclicPerm.symm s) →ₗ[K] CWSpace K q s :=
  fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 1, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 2, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)

private noncomputable def cwBaseToCyclic
    (K : Type u) [Field K] (q : ℕ) :
    ∀ s : Fin 3,
      CWSpace K q s →ₗ[K] CWSpace K q (cyclicPerm.symm s) :=
  fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 1, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 2, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)

private theorem map_cyclic_reindex_CWMonom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwCyclicToBase K q)
      ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWMonom K q a b c)) = CWMonom K q c a b := by
  unfold CWMonom
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem map_cyclic_reindex_CWTensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwCyclicToBase K q)
      ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWTensor K q)) = CWTensor K q := by
  unfold CWTensor
  simp only [map_add, map_sum, map_cyclic_reindex_CWMonom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q M O M + CWMonom K q M M O + CWMonom K q O M M) =
      ∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    abel
  rw [hsum]
  abel

private theorem map_baseToCyclic_CWMonom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwBaseToCyclic K q) (CWMonom K q a b c) =
      (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWMonom K q b c a) := by
  unfold CWMonom
  rw [PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem map_baseToCyclic_CWTensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwBaseToCyclic K q) (CWTensor K q) =
      (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWTensor K q) := by
  unfold CWTensor
  simp only [map_add, map_sum, map_baseToCyclic_CWMonom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm) (CWMonom K q M M O) +
        (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm) (CWMonom K q O M M) +
        (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm) (CWMonom K q M O M)) =
      ∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm) (CWMonom K q O M M) +
        (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm) (CWMonom K q M O M) +
        (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm) (CWMonom K q M M O) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    abel
  rw [hsum]
  abel

theorem CWObj_permObj_cyclic_iso
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (CWObj K q)) (CWObj K q) := by
  constructor
  · exact ⟨cwBaseToCyclic K q, map_baseToCyclic_CWTensor K q⟩
  · exact ⟨cwCyclicToBase K q, map_cyclic_reindex_CWTensor K q⟩

private noncomputable def cwSwapToBase
    (K : Type u) [Field K] (q : ℕ) :
    ∀ s : Fin 3,
      CWSpace K q (swapFirstTwoPerm.symm s) →ₗ[K] CWSpace K q s :=
  fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 1, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 2, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)

private noncomputable def cwBaseToSwap
    (K : Type u) [Field K] (q : ℕ) :
    ∀ s : Fin 3,
      CWSpace K q s →ₗ[K] CWSpace K q (swapFirstTwoPerm.symm s) :=
  fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 1, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | 2, _ => change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)

private theorem map_swap_reindex_CWMonom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwSwapToBase K q)
      ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWMonom K q a b c)) = CWMonom K q b a c := by
  unfold CWMonom
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem map_swap_reindex_CWTensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwSwapToBase K q)
      ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWTensor K q)) = CWTensor K q := by
  unfold CWTensor
  simp only [map_add, map_sum, map_swap_reindex_CWMonom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q M O M + CWMonom K q O M M + CWMonom K q M M O) =
      ∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    abel
  rw [hsum]
  abel

private theorem map_baseToSwap_CWMonom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwBaseToSwap K q) (CWMonom K q a b c) =
      (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWMonom K q b a c) := by
  unfold CWMonom
  rw [PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem map_baseToSwap_CWTensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwBaseToSwap K q) (CWTensor K q) =
      (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWTensor K q) := by
  unfold CWTensor
  simp only [map_add, map_sum, map_baseToSwap_CWMonom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm) (CWMonom K q M O M) +
        (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm) (CWMonom K q O M M) +
        (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm) (CWMonom K q M M O)) =
      ∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm) (CWMonom K q O M M) +
        (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm) (CWMonom K q M O M) +
        (PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm) (CWMonom K q M M O) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    abel
  rw [hsum]
  abel

theorem CWObj_permObj_swap_iso
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm (CWObj K q)) (CWObj K q) := by
  constructor
  · exact ⟨cwBaseToSwap K q, map_baseToSwap_CWTensor K q⟩
  · exact ⟨cwSwapToBase K q, map_swap_reindex_CWTensor K q⟩

end MME

open MME

universe u

private theorem permObj_trans_iso_for_solution
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (e.trans e') X).V))
      (TensorObj.permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj e' (TensorObj.permObj e X)).V))
      (TensorObj.permObj e' (TensorObj.permObj e X)).t
    exact hmap.trans ht

private theorem CWObj_permObj_cyclic_sq_iso_for_solution
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (CWObj K q))
      (CWObj K q) := by
  have hcyc := MME.CWObj_permObj_cyclic_iso K q
  exact (permObj_trans_iso_for_solution cyclicPerm cyclicPerm (CWObj K q)).symm |>.trans
    ((TensorObj.permObj_isomorphic cyclicPerm hcyc).trans hcyc)

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization
        (TensorObj.kron (CWObj K q) (CWObj K q)))
      ((TensorObj.kron (CWObj K q) (CWObj K q)).kronPow 6) := by
  let C : TensorObj K 3 := CWObj K q
  let T : TensorObj K 3 := TensorObj.kron C C
  have hcycC : TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm C) C := by
    simpa [C] using MME.CWObj_permObj_cyclic_iso K q
  have hcyc2C : TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) C) C := by
    simpa [C] using CWObj_permObj_cyclic_sq_iso_for_solution K q
  have hswapC : TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm C) C := by
    simpa [C] using MME.CWObj_permObj_swap_iso K q
  have hcycT : TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm T) T := by
    exact (TensorObj.permObj_kron_iso cyclicPerm C C).trans
      (TensorQ.mul_respects_iso hcycC hcycC)
  have hcyc2T : TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T) T := by
    exact (TensorObj.permObj_kron_iso
      (cyclicPerm.trans cyclicPerm) C C).trans
      (TensorQ.mul_respects_iso hcyc2C hcyc2C)
  have hswapT : TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm T) T := by
    exact (TensorObj.permObj_kron_iso swapFirstTwoPerm C C).trans
      (TensorQ.mul_respects_iso hswapC hswapC)
  have hcyclicQ :
      TensorQ.toQ (cyclicSymmetrization T) = (TensorQ.toQ T) ^ 3 := by
    rw [cyclicSymmetrization_eq_public_perm]
    change TensorQ.toQ (TensorObj.kron T
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm T)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))) = _
    rw [TensorQ.toQ_kron T
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm T)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))]
    rw [TensorQ.toQ_kron
      (TensorObj.permObj cyclicPerm T)
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T)]
    rw [(TensorQ.toQ_eq_iff).2 hcycT, (TensorQ.toQ_eq_iff).2 hcyc2T]
    ring
  have hswapTQ :
      TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ T) = TensorQ.toQ T := by
    change TensorQ.toQ (TensorObj.permObj swapFirstTwoPerm T) = TensorQ.toQ T
    exact (TensorQ.toQ_eq_iff).2 hswapT
  have hswapCyclicQ :
      TensorQ.toQ (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization T)) = (TensorQ.toQ T) ^ 3 := by
    change TensorQ.permAut swapFirstTwoPerm
      (TensorQ.toQ (cyclicSymmetrization T)) = (TensorQ.toQ T) ^ 3
    rw [hcyclicQ, map_pow, hswapTQ]
  apply (TensorQ.toQ_eq_iff).1
  change TensorQ.toQ (sixSymmetrization T) = TensorQ.toQ (T.kronPow 6)
  rw [show sixSymmetrization T =
      TensorObj.kron (cyclicSymmetrization T)
        (TensorObj.permObj swapFirstTwoPerm (cyclicSymmetrization T)) from rfl]
  rw [TensorQ.toQ_kron, TensorQ.toQ_kronPow, hcyclicQ, hswapCyclicQ]
  ring
