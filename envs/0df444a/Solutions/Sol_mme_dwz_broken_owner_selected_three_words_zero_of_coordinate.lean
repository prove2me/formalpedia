-- Prove2me | solution 1 for mme_dwz_broken_owner_selected_three_words_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:03:38.543331+00:00
-- url     : https://prove2.me/submissions/4862a80a-1edc-471e-81f9-12b0eb466729

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_dwz_broken_owner_three_words_data
import Theorems.Thm_mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate
import Theorems.Thm_mme_dwz_broken_owner_three_words_fine_grade_families_eq
import Theorems.Thm_mme_dwz_broken_owner_three_words_maps_pointwise

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 12000

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer)
    (hzero : ∃ r : Fin N,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ ![
          MME.DWZStep1Support.fineSplitGrade
            (addressModeLeftGrade x r)
            (addressModeRightGrade x r),
          MME.DWZStep1Support.fineSplitGrade
            (addressModeLeftGrade y r)
            (addressModeRightGrade y r),
          MME.DWZStep1Support.fineSplitGrade
            (z r).leftGrade (z r).rightGrade] i) = 0) :
    let G := brokenAddressGrading K m outer copy
    let sx := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 0) id {x}
    let sy := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 1) id {y}
    let sz := DWZComponentRestriction.basisLabelProjection
      (coarseAddressZBasis K outer) id {z}
    let selected : ∀ i : Fin 3,
        (coarseAddressObj K outer).V i →ₗ[K]
          (coarseAddressObj K outer).V i :=
      Function.update
        (Function.update
          (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
    PiTensorProduct.map
      (fun i ↦ (G.blockProj i 0).comp (selected i))
      (coarseAddressObj K outer).t = 0 := by
  classical
  obtain ⟨r, hr⟩ := hzero
  have hgrade : (cwSquareFineSplitGrading K 6).blockTensor
      (brokenOwnerThreeWordsFineGradeFamily x y z r) = 0 := by
    rw [mme_dwz_broken_owner_three_words_fine_grade_families_eq
      x y z r]
    exact hr
  have hword :=
    mme_dwz_coarseAddress_selected_mode_words_postmap_eq_zero_of_coordinate
      (K := K) outer (brokenOwnerThreeWordsWord x y z)
      (fun i ↦ (brokenAddressGrading K m outer copy).blockProj i 0)
      r hgrade
  change PiTensorProduct.map
      (brokenOwnerThreeWordsWordMap K m outer copy x y z)
      (coarseAddressObj K outer).t = 0 at hword
  dsimp only
  change PiTensorProduct.map
      (brokenOwnerThreeWordsSelectedMap K m outer copy x y z)
      (coarseAddressObj K outer).t = 0
  have hmaps :
      brokenOwnerThreeWordsWordMap K m outer copy x y z =
        brokenOwnerThreeWordsSelectedMap K m outer copy x y z := by
    funext i
    exact mme_dwz_broken_owner_three_words_maps_pointwise
      m outer copy x y z i
  rw [← hmaps]
  exact hword
