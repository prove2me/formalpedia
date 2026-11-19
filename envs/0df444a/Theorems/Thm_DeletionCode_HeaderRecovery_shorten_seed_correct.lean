-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_shorten_seed_correct
-- name    : DeletionCode.HeaderRecovery.shorten_seed_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:15.84633+00:00
-- url     : https://prove2.me/theorems/259f39f5-6528-4879-8982-2ebc99654ee2
-- title:
--   Header Recovery: shorten seed correct
-- statement:
--   The Header Recovery construction uses the shorten seed correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L149-L172
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L149-L172

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.shorten_seed_correct (p : Letters) (ell k : ℕ) (seed : Seed)
    (extra : Bool) (hseed : Agree p seed.offset seed.bits 0 k)
    (hextra : seed.offset ≤ ell → ell < seed.offset + k →
      extra = deleteAt p ell (seed.offset + k - 1)) :
    Agree (deleteAt p ell) (shortenSeed ell k seed extra).offset
      (shortenSeed ell k seed extra).bits 0 k := by sorry
