-- Prove2me | solution 1 for mme_dwz_q6_211_normalized_restricted_primary_hash_Ctensor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:36:26.631624+00:00
-- url     : https://prove2.me/submissions/6dae8b14-6519-4adc-89ba-e8cb67ba5d40

import Theorems.Thm_mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
import Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_isomorphisms
import Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_permutation
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

private theorem permObj_trans_iso_pair_row211_certificate
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

private theorem permObj_refl_iso_row211_certificate
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
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (restrictedComponentPower K (14 : Fin 15) m))
        A H (6 ^ (4 * G + 2 * L))) := by
  classical
  let G0 := dwzQ6CoupledGrading K
  let stars : Fin A → TensorObj K 3 := starObj G0 family
  have hrestrict : TensorObj.Restrict (TensorObj.bigAdd stars)
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (restrictedComponentPower K (14 : Fin 15) m)) := by
    have hraw : TensorObj.Restrict
        (TensorObj.permObj cyclicPerm (TensorObj.bigAdd stars))
        (restrictedComponentPower K (14 : Fin 15) m) := by
      simpa [G0, stars] using
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
      have htrans := permObj_trans_iso_pair_row211_certificate cyclicPerm
        (cyclicPerm.trans cyclicPerm) (TensorObj.bigAdd stars)
      rw [hcycle] at htrans
      exact htrans.trans
        (permObj_refl_iso_row211_certificate (TensorObj.bigAdd stars))
    exact TensorObj.Restrict.trans horient.2 hpermuted
  have hstar :=
    mme_primary_hash_family_sharedZ_star_grading_components G0 family
  obtain ⟨h000, h111, h012, h102⟩ :=
    mme_dwz_q6_explicit_coupled_four_block_isomorphisms (K := K)
  refine ⟨{
    star := stars
    restrict := hrestrict
    certificate := ?_
  }⟩
  intro a
  let grading : (stars a).TypeGrading (H + 1) :=
    starGrading G0 family a
  have hsupported : ∀ σ : Fin 3 → Fin (H + 1),
      σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
        grading.blockTensor σ = 0 := by
    simpa [grading, stars] using (hstar a).1
  have hstarComponent : ∀ h : Fin H,
      TensorObj.Isomorphic
        (componentObj G0 family a h)
        (grading.blockSubtensor (cTensorOneHOneAddress H h)) := by
    intro h
    simpa [grading, stars] using (hstar a).2 h
  have hcomponent (h : Fin H) :
      ∃ x y z : ℕ,
        TensorObj.Isomorphic (MMObj K x y z)
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x * y * z = 6 ^ (4 * G + 2 * L) := by
    obtain ⟨x, y, z, hiso, hvolume⟩ :=
      mme_coupled_four_block_exact_address_component_certificate
        6 (1036722900000000 * m) L G
        (coupledObj K 6) G0 h000 h111 h012 h102
        (family.entry (a, h))
    have hlocal : TensorObj.Isomorphic (MMObj K x y z)
        (componentObj G0 family a h) := by
      simpa [componentObj] using hiso
    exact ⟨x, y, z, hlocal.trans (hstarComponent h), hvolume⟩
  let x (h : Fin H) : ℕ := Classical.choose (hcomponent h)
  have hyz (h : Fin H) :
      ∃ y z : ℕ,
        TensorObj.Isomorphic (MMObj K (x h) y z)
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y * z = 6 ^ (4 * G + 2 * L) :=
    Classical.choose_spec (hcomponent h)
  let y (h : Fin H) : ℕ := Classical.choose (hyz h)
  have hz (h : Fin H) :
      ∃ z : ℕ,
        TensorObj.Isomorphic (MMObj K (x h) (y h) z)
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y h * z = 6 ^ (4 * G + 2 * L) :=
    Classical.choose_spec (hyz h)
  let z (h : Fin H) : ℕ := Classical.choose (hz h)
  have hxyz (h : Fin H) :
      TensorObj.Isomorphic (MMObj K (x h) (y h) (z h))
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y h * z h = 6 ^ (4 * G + 2 * L) :=
    Classical.choose_spec (hz h)
  exact {
    grading := grading
    supported := hsupported
    m := x
    n := y
    p := z
    component := fun h ↦ (hxyz h).1
    common_volume := fun h ↦ (hxyz h).2
  }
