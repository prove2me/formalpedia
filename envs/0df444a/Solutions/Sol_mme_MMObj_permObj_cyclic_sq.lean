-- Prove2me | solution 1 for mme_MMObj_permObj_cyclic_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:43:57.960195+00:00
-- url     : https://prove2.me/submissions/0381475f-fe9f-46e5-a717-ac640e0cfc9f

import Definitions.Def_mme_permutation

open MME PiTensorProduct

universe u

namespace MME.TensorObj

private theorem permObj_trans_iso_local
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (permObj e' (permObj e X))
      (permObj (e.trans e') X) := by
  have ht : (permObj e' (permObj e X)).t =
      (permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (permObj (e.trans e') X).V))
      (permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (permObj e' (permObj e X)).V))
      (permObj e' (permObj e X)).t
    exact hmap.trans ht

private theorem MMObj_permObj_cyclic_sq_local
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p))
      (MMObj K m p n) := by
  have htrans :=
    (permObj_trans_iso_local cyclicPerm cyclicPerm
      (MMObj K n m p)).symm
  have hfirst := permObj_isomorphic cyclicPerm
    (MMObj_permObj_cyclic (K := K) n m p)
  have hsecond := MMObj_permObj_cyclic (K := K) p n m
  exact htrans.trans (hfirst.trans hsecond)

end MME.TensorObj

theorem solution
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj (MME.cyclicPerm.trans MME.cyclicPerm)
        (MME.MMObj K n m p))
      (MME.MMObj K m p n) := by
  exact MME.TensorObj.MMObj_permObj_cyclic_sq_local n m p
