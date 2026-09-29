-- Prove2me | solution 1 for mme_dwz_step1_mixed_selected_word_fine_grades
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:27:17.263881+00:00
-- url     : https://prove2.me/submissions/0967fcb7-05e8-4df8-a539-65e2285bd35c

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

theorem solution
    {K : Type u} [Field K]
    {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1)
    (r : Fin L) :
    (fun i ↦ MME.DWZStep1Support.fineSplitGrade
      ((step1MixedSelectedWord reindex edge competitor owner W x y i r).leftGrade)
      ((step1MixedSelectedWord reindex edge competitor owner W x y i r).rightGrade)) =
    (fun i ↦ MME.DWZStep1Support.fineSplitGrade
      (![addressModeLeftGrade x r,
        addressModeLeftGrade y r,
        (W r).leftGrade] i)
      (![addressModeRightGrade x r,
        addressModeRightGrade y r,
        (W r).rightGrade] i)) := by
  funext i
  fin_cases i <;> rfl
