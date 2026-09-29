-- Prove2me | solution 1 for mme_dwz_step1_rejected_singletons_zero_of_coordinate_word_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:16:30.351302+00:00
-- url     : https://prove2.me/submissions/67d1549b-38e2-4817-911c-f26a930776ed

import Definitions.Def_mme_dwz_step1_rejected_singleton_properties
import Theorems.Thm_mme_dwz_step1_x_rejected_singletons_zero_of_coordinate_word_zero
import Theorems.Thm_mme_dwz_step1_y_rejected_singletons_zero_of_coordinate_word_zero

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (hCoordinateZero : ∀
      (x : AddressModeWord outer 0)
      (y : AddressModeWord outer 1)
      (z : AddressZWord outer),
      (∃ r : Fin N,
        (cwSquareFineSplitGrading K 6).blockTensor
          (fun i ↦ ![
            MME.DWZStep1Support.fineSplitGrade
              (addressModeLeftGrade x r)
              (addressModeRightGrade x r),
            MME.DWZStep1Support.fineSplitGrade
              (addressModeLeftGrade y r)
              (addressModeRightGrade y r),
            MME.DWZStep1Support.fineSplitGrade
              (z r).leftGrade (z r).rightGrade] i) = 0) →
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
        (coarseAddressObj K outer).t = 0) :
    (∀ (x : AddressModeWord outer 0),
      ¬ addressXWordPassesStep1 m outer x →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let singleton := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 0) id {x}
      PiTensorProduct.map
        (Function.update base 0 ((base 0).comp singleton))
        (coarseAddressObj K outer).t = 0) ∧
    (∀ (y : AddressModeWord outer 1),
      ¬ addressYWordPassesStep1 m outer y →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let xMaps := Function.update base 0
        ((base 0).comp (addressXStep1Projector K m outer))
      let singleton := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 1) id {y}
      PiTensorProduct.map
        (Function.update xMaps 1 ((xMaps 1).comp singleton))
        (coarseAddressObj K outer).t = 0) := by
  change BrokenOwnerCoordinateZeroProperty K m outer copy at hCoordinateZero
  change Step1XRejectedSingletonZeroProperty K m outer copy ∧
    Step1YRejectedSingletonZeroProperty K m outer copy
  exact ⟨
    mme_dwz_step1_x_rejected_singletons_zero_of_coordinate_word_zero
      m outer copy hCoordinateZero,
    mme_dwz_step1_y_rejected_singletons_zero_of_coordinate_word_zero
      m outer copy hCoordinateZero⟩
