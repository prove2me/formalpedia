-- Prove2me | solution 1 for mme_dwz_broken_owner_three_words_fine_grade_families_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:59:47.178974+00:00
-- url     : https://prove2.me/submissions/082a366e-c146-4606-adb1-711671e74f3f

import Definitions.Def_mme_dwz_broken_owner_three_words_data

open MME Module
open MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N : ℕ} {outer : Fin N → Fin 15}
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (r : Fin N) :
    brokenOwnerThreeWordsFineGradeFamily x y z r =
      brokenOwnerThreeWordsVectorFineGradeFamily x y z r := by
  funext i
  fin_cases i <;> rfl
