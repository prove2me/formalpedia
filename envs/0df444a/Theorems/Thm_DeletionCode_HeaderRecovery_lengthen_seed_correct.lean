-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_lengthen_seed_correct
-- name    : DeletionCode.HeaderRecovery.lengthen_seed_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:44.463062+00:00
-- url     : https://prove2.me/theorems/455b7c30-a0b6-4cf1-959c-1702a2f8eb23
-- title:
--   Header Recovery: lengthen seed correct
-- statement:
--   The Header Recovery construction uses the lengthen seed correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L174-L194
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L174-L194

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.lengthen_seed_correct (p : Letters) (ell k : ℕ) (seed : Seed)
    (bit : Bool) (hseed : Agree p seed.offset seed.bits 0 k) :
    Agree (insertAt p ell bit) (lengthenSeed ell k seed bit).offset
      (lengthenSeed ell k seed bit).bits 0 k := by sorry
