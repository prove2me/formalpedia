-- Prove2me | solution 1 for mme_sixSymmetrization_isomorphic_cyclic_paired_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:15:08.40083+00:00
-- url     : https://prove2.me/submissions/9a52fbd0-ad3f-45ea-8531-875c8d75f154

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

private theorem permObj_trans_iso_pair
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

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (sixSymmetrization T)
      (cyclicSymmetrization
        (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))) := by
  let c2 : Equiv.Perm (Fin 3) := cyclicPerm.trans cyclicPerm
  let q : TensorQ K 3 := TensorQ.toQ T
  have hcycQ (X : TensorObj K 3) :
      TensorQ.toQ (cyclicSymmetrization X) =
        TensorQ.toQ X *
          (TensorQ.permAut cyclicPerm (TensorQ.toQ X) *
            TensorQ.permAut c2 (TensorQ.toQ X)) := by
    rw [cyclicSymmetrization_eq_public_perm]
    rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
    rfl
  have hcomp (e e' : Equiv.Perm (Fin 3)) :
      TensorQ.permAut e' (TensorQ.permAut e q) =
        TensorQ.permAut (e.trans e') q := by
    change TensorQ.toQ (TensorObj.permObj e'
        (TensorObj.permObj e T)) =
      TensorQ.toQ (TensorObj.permObj (e.trans e') T)
    exact TensorQ.toQ_eq_iff.mpr (permObj_trans_iso_pair e e' T)
  have hsc : cyclicPerm.trans swapFirstTwoPerm =
      swapFirstTwoPerm.trans c2 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hsc2 : c2.trans swapFirstTwoPerm =
      swapFirstTwoPerm.trans cyclicPerm := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  apply TensorQ.toQ_eq_iff.mp
  change TensorQ.toQ (sixSymmetrization T) =
    TensorQ.toQ
      (cyclicSymmetrization
        (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T)))
  rw [show sixSymmetrization T =
      TensorObj.kron (cyclicSymmetrization T)
        (TensorObj.permObj swapFirstTwoPerm
          (cyclicSymmetrization T)) from rfl]
  rw [TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  rw [hcycQ, hcycQ]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  change
    (q * (TensorQ.permAut cyclicPerm q * TensorQ.permAut c2 q)) *
        (TensorQ.permAut swapFirstTwoPerm q *
          (TensorQ.permAut swapFirstTwoPerm
              (TensorQ.permAut cyclicPerm q) *
            TensorQ.permAut swapFirstTwoPerm
              (TensorQ.permAut c2 q))) = _
  rw [hcomp cyclicPerm swapFirstTwoPerm,
    hcomp c2 swapFirstTwoPerm,
    hcomp swapFirstTwoPerm cyclicPerm,
    hcomp swapFirstTwoPerm c2,
    hsc, hsc2]
  ring
