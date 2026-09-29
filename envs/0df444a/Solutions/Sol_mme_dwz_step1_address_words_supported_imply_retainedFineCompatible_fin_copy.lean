-- Prove2me | solution 1 for mme_dwz_step1_address_words_supported_imply_retainedFineCompatible_fin_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T02:45:50.68426+00:00
-- url     : https://prove2.me/submissions/dad37029-65d2-41fc-bd65-d23810fe28d5

import Theorems.Thm_mme_dwz_step1_address_words_supported_imply_retainedFineCompatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open MME.DWZSourceAligned

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {n N : ℕ}
    (outer : Fin n → Fin N → Fin 15)
    (owner competitor : Fin n)
    (hCommonZ : ∀ t,
      DWZSquare.shapeZ (outer owner t) =
        DWZSquare.shapeZ (outer competitor t))
    (xWord : AddressModeWord (outer competitor) 0)
    (yWord : AddressModeWord (outer competitor) 1)
    (zWord : AddressZWord (outer owner))
    (hX : addressXWordPassesStep1 m (outer competitor) xWord)
    (hY : addressYWordPassesStep1 m (outer competitor) yWord)
    (hUseful : addressWordUseful m (outer owner) zWord)
    (hSupported : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ fineSplitGrade
          (![addressModeLeftGrade xWord t,
            addressModeLeftGrade yWord t,
            (zWord t).leftGrade] i)
          (![addressModeRightGrade xWord t,
            addressModeRightGrade yWord t,
            (zWord t).rightGrade] i)) ≠ 0) :
    retainedFineCompatible m outer
      (fun t ↦ fineSplitGrade (zWord t).leftGrade (zWord t).rightGrade)
      competitor := by
  let Copy := ULift.{u} (Fin n)
  let outer' : Copy → Fin N → Fin 15 := fun j ↦ outer j.down
  let owner' : Copy := ULift.up owner
  let competitor' : Copy := ULift.up competitor
  have hCommonZ' : ∀ t,
      DWZSquare.shapeZ (outer' owner' t) =
        DWZSquare.shapeZ (outer' competitor' t) := hCommonZ
  have h :=
    mme_dwz_step1_address_words_supported_imply_retainedFineCompatible
      (K := K) (Copy := Copy) (N := N)
      m outer' owner' competitor' hCommonZ'
        xWord yWord zWord hX hY hUseful hSupported
  exact h
