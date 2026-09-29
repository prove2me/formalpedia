-- Prove2me | solution 1 for mme_dwz_step1FilteredMixedSingletonMaps_eq_sourceFamily_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:12:31.175718+00:00
-- url     : https://prove2.me/submissions/5c6e2e79-88a8-4d03-8ac7-4319ec5732f0

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (i : Fin 3) :
    step1FilteredMixedSingletonMaps K m reindex q edge
        competitor owner W i =
      step1MixedSourceFamilySingletonMaps K m reindex q edge
        competitor owner W i := by
  fin_cases i
  · exact congrArg
      (fun g => (step1FilteredMixedSingletonAddressPost K m reindex q edge
        competitor owner W 0).comp g)
      (mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
        reindex edge competitor owner 0)
  · exact congrArg
      (fun g => (step1FilteredMixedSingletonAddressPost K m reindex q edge
        competitor owner W 1).comp g)
      (mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
        reindex edge competitor owner 1)
  · exact congrArg
      (fun g => (step1FilteredMixedSingletonAddressPost K m reindex q edge
        competitor owner W 2).comp g)
      (mme_dwz_step1MixedCoarseProj_eq_owner_gradedAddressProj
        reindex edge competitor owner 2)
