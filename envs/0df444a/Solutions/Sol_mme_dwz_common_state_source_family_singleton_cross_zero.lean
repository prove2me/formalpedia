-- Prove2me | solution 1 for mme_dwz_common_state_source_family_singleton_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:26:18.98769+00:00
-- url     : https://prove2.me/submissions/922e6006-96eb-4fb2-b226-542d947498ec

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_step1_mixed_selected_support_property
import Theorems.Thm_mme_dwz_common_state_step1_filtered_mixed_singleton_zero_of_selected_support
import Theorems.Thm_mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply

open MME Module PiTensorProduct

universe u uR uI uS uT

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

private theorem piTensorProduct_map_eq_of_pointwise
    {R : Type uR} [CommSemiring R]
    {ι : Type uI}
    {S : ι → Type uS} [∀ i, AddCommMonoid (S i)]
      [∀ i, Module R (S i)]
    {T : ι → Type uT} [∀ i, AddCommMonoid (T i)]
      [∀ i, Module R (T i)]
    (f g : ∀ i, S i →ₗ[R] T i)
    (h : ∀ i, f i = g i)
    (x : PiTensorProduct R S) :
    PiTensorProduct.map f x = PiTensorProduct.map g x := by
  have hfg : f = g := funext h
  rw [hfg]

private theorem sourceFamilySingletonZero_of_ownerIndex_eq
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (owners : Fin 3 → Fin n)
    (hOwners : step1MixedOwnerIndex competitor owner = owners)
    (hOwnerTwo : owner = owners 2)
    (W : AddressZWord (sourceWord reindex edge owner))
    (hZero :
      PiTensorProduct.map
          (step1MixedSourceFamilySingletonMaps K m reindex q edge
            competitor owner W)
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0) :
    let Source : TensorObj K 3 :=
      (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L
    let maps : ∀ i : Fin 3, Source.V i →ₗ[K]
        (brokenAddressObj K m
          (sourceWord reindex edge (owners i))
          (commonStateBrokenCopy m reindex q edge (owners i))).V i :=
      fun i ↦ step1FilteredBrokenSourceMaps K m
        (sourceWord reindex edge (owners i))
        (commonStateBrokenCopy m reindex q edge (owners i)) i
    let singleton :=
      DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K (sourceWord reindex edge owner)) id {W}
    let selectedZ :=
      (((step1FilteredBrokenAddressMaps K m
          (sourceWord reindex edge owner)
          (commonStateBrokenCopy m reindex q edge owner) 2).comp
        singleton).comp
        (gradedAddressProj (cwSquareCanonicalGrading K 6) L
          (coarseAddress (sourceWord reindex edge owner)) 2))
    PiTensorProduct.map
      (Function.update maps 2 (hOwnerTwo ▸ selectedZ)) Source.t = 0 := by
  subst owners
  cases hOwnerTwo
  exact hZero

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hBucket : ∀ j, edge j ∈ dwzTable2AffineHashBucket S A q)
    (js : Fin 3 → Fin n)
    (h01 : js 0 = js 1) (h02 : js 0 ≠ js 2)
    (W : AddressZWord (sourceWord reindex edge (js 2)))
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge (js 2))
      (commonStateBrokenCopy m reindex q edge (js 2)) W) :
    let Source : TensorObj K 3 :=
      (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L
    let maps : ∀ i : Fin 3, Source.V i →ₗ[K]
        (brokenAddressObj K m
          (sourceWord reindex edge (js i))
          (commonStateBrokenCopy m reindex q edge (js i))).V i :=
      fun i ↦ step1FilteredBrokenSourceMaps K m
        (sourceWord reindex edge (js i))
        (commonStateBrokenCopy m reindex q edge (js i)) i
    let singleton :=
      DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K (sourceWord reindex edge (js 2))) id {W}
    let selectedZ :=
      (((step1FilteredBrokenAddressMaps K m
          (sourceWord reindex edge (js 2))
          (commonStateBrokenCopy m reindex q edge (js 2)) 2).comp
        singleton).comp
        (gradedAddressProj (cwSquareCanonicalGrading K 6) L
          (coarseAddress (sourceWord reindex edge (js 2))) 2))
    PiTensorProduct.map (Function.update maps 2 selectedZ) Source.t = 0 := by
  classical
  have hOwnerIndex :
      step1MixedOwnerIndex (js 0) (js 2) = js := by
    funext i
    fin_cases i
    · rfl
    · exact h01
    · rfl
  have hRaw :=
    mme_dwz_common_state_step1_filtered_mixed_singleton_zero_of_selected_support
      (K := K) m reindex hpodd S hSrange hSfree A q edge hBucket
        (js 0) (js 2) h02 W hSurvives
        (mme_dwz_step1_mixed_selected_support_property
          (K := K) m reindex q edge (js 0) (js 2) W)
  have hMapsValue :
      PiTensorProduct.map
          (step1FilteredMixedSingletonMaps K m reindex q edge
            (js 0) (js 2) W)
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t =
        PiTensorProduct.map
          (step1MixedSourceFamilySingletonMaps K m reindex q edge
            (js 0) (js 2) W)
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t := by
    apply piTensorProduct_map_eq_of_pointwise
    intro i
    exact mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply
      m reindex q edge (js 0) (js 2) W i
  rw [hMapsValue] at hRaw
  exact sourceFamilySingletonZero_of_ownerIndex_eq
    m reindex q edge (js 0) (js 2) js hOwnerIndex rfl W hRaw
