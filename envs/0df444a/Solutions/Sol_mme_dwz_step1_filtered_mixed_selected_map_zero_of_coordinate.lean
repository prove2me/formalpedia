-- Prove2me | solution 1 for mme_dwz_step1_filtered_mixed_selected_map_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:23:06.053951+00:00
-- url     : https://prove2.me/submissions/003bbfc9-46e8-4da1-801b-57e50a178fae

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
import Theorems.Thm_mme_dwz_step1_mixed_selected_full_map_zero_of_coordinate
import Theorems.Thm_mme_dwz_step1_mixed_selected_full_maps_eq_filtered

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1)
    (r : Fin L)
    (hFineZero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ MME.DWZStep1Support.fineSplitGrade
        (![addressModeLeftGrade x r,
          addressModeLeftGrade y r,
          (W r).leftGrade] i)
        (![addressModeRightGrade x r,
          addressModeRightGrade y r,
          (W r).rightGrade] i)) = 0) :
    PiTensorProduct.map
      (step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  have h := mme_dwz_step1_mixed_selected_full_map_zero_of_coordinate
    m reindex q edge competitor owner W x y r hFineZero
  rw [mme_dwz_step1_mixed_selected_full_maps_eq_filtered
    m reindex q edge competitor owner W x y] at h
  exact h
