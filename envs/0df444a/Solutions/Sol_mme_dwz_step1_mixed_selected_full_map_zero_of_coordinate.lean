-- Prove2me | solution 1 for mme_dwz_step1_mixed_selected_full_map_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:23:11.090124+00:00
-- url     : https://prove2.me/submissions/005a1c04-af2d-4080-94de-5c3cf4c15ec5

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
import Theorems.Thm_mme_dwz_step1_mixed_selected_address_map_zero_of_coordinate
import Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 14000

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
      (step1MixedSelectedFullMaps K m reindex q edge
        competitor owner W x y)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  have hAddress :=
    mme_dwz_step1_mixed_selected_address_map_zero_of_coordinate
      m reindex q edge competitor owner W x y r hFineZero
  let address := step1MixedAddress reindex edge competitor owner
  let selectedMaps := step1MixedSelectedAddressMaps K m reindex q edge
    competitor owner W x y
  let coarseProj := gradedAddressProj
    (cwSquareCanonicalGrading K 6) L address
  change PiTensorProduct.map
      (fun i ↦ (selectedMaps i).comp (coarseProj i))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  rw [show PiTensorProduct.map coarseProj
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t =
      (gradedAddressBlock (cwSquareCanonicalGrading K 6) address).t by
    exact mme_gradedAddressProj_preserves_kronPow_tensor
      (cwSquareCanonicalGrading K 6) address]
  exact hAddress
