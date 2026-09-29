-- Prove2me | solution 1 for mme_dwz_q6_211_normalized_primary_hash_star_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:36:38.999277+00:00
-- url     : https://prove2.me/submissions/35f7e309-ad56-43d4-ad58-93053c3ec9ad

import Theorems.Thm_mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
import Definitions.Def_mme_permutation
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

private theorem permObj_trans_iso_pair_row211
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

private theorem permObj_refl_iso_row211
    {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj (Equiv.refl (Fin d)) X) X := by
  have ht : (TensorObj.permObj (Equiv.refl (Fin d)) X).t = X.t := by
    change (PiTensorProduct.reindex K X.V (Equiv.refl (Fin d))) X.t = X.t
    rw [PiTensorProduct.reindex_refl]
    rfl
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id (R := K) (s := X.V)) X.t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (Equiv.refl (Fin d)) X).V))
      (TensorObj.permObj (Equiv.refl (Fin d)) X).t
    exact hmap.trans ht

theorem solution
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (starObj (dwzQ6CoupledGrading K) family))
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (restrictedComponentPower K (14 : Fin 15) m)) := by
  let stars : Fin A → TensorObj K 3 :=
    starObj (dwzQ6CoupledGrading K) family
  have hraw : TensorObj.Restrict
      (TensorObj.permObj cyclicPerm (TensorObj.bigAdd stars))
      (restrictedComponentPower K (14 : Fin 15) m) := by
    simpa [stars] using
      mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
        (K := K) m L G A H family
  have hpermuted :=
    TensorObj.permObj_restrict (cyclicPerm.trans cyclicPerm) hraw
  have hcycle : cyclicPerm.trans (cyclicPerm.trans cyclicPerm) =
      Equiv.refl (Fin 3) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have horient : TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (TensorObj.permObj cyclicPerm (TensorObj.bigAdd stars)))
      (TensorObj.bigAdd stars) := by
    have htrans := permObj_trans_iso_pair_row211 cyclicPerm
      (cyclicPerm.trans cyclicPerm) (TensorObj.bigAdd stars)
    rw [hcycle] at htrans
    exact htrans.trans (permObj_refl_iso_row211 (TensorObj.bigAdd stars))
  exact TensorObj.Restrict.trans horient.2 hpermuted
