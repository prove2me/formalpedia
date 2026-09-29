-- Prove2me | solution 1 for mme_dwz_common_state_mixed_singleton_zero_of_fine_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:50:10.512267+00:00
-- url     : https://prove2.me/submissions/93236cdc-cfbe-495f-96cf-4d494a91a83f

import Theorems.Thm_mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
import Theorems.Thm_mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

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
    (js : Fin 3 → Fin n) (h01 : js 0 = js 1) (h02 : js 0 ≠ js 2)
    (W : AddressZWord (sourceWord reindex edge (js 2)))
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge (js 2))
      (commonStateBrokenCopy m reindex q edge (js 2)) W)
    {V : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (post : ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (fun i r ↦ coarseAddress
          (sourceWord reindex edge (js i)) i r)).V i →ₗ[K] V i)
    (hFine :
      let x := PiTensorProduct.map
        (fun i ↦ (post i).comp
          (gradedAddressProj (cwSquareCanonicalGrading K 6) L
            (fun i r ↦ coarseAddress
              (sourceWord reindex edge (js i)) i r) i))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t
      x ≠ 0 →
      ∀ hUseful : addressWordUseful m
          (sourceWord reindex edge (js 2)) W,
        MME.DWZStep2Source.retainedFineCompatible m
          (sourceWord reindex edge)
          (fun t ↦ MME.DWZStep1Support.fineSplitGrade
            ((addressUsefulBlock m
              (sourceWord reindex edge (js 2)) W hUseful).1 t).1
            ((addressUsefulBlock m
              (sourceWord reindex edge (js 2)) W hUseful).1 t).2)
          (js 0)) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (gradedAddressProj (cwSquareCanonicalGrading K 6) L
            (fun i r ↦ coarseAddress
              (sourceWord reindex edge (js i)) i r) i))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  let x := PiTensorProduct.map
    (fun i ↦ (post i).comp
      (gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (fun i r ↦ coarseAddress
          (sourceWord reindex edge (js i)) i r) i))
    ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t
  change x = 0
  apply mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor
    m reindex q edge (js 2) (js 0) W x hSurvives h02
  intro hx hUseful
  exact mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
    m reindex hpodd S hSrange hSfree A q edge hBucket js h01
      (addressUsefulBlock m (sourceWord reindex edge (js 2)) W hUseful)
      post hx (hFine hx hUseful)
