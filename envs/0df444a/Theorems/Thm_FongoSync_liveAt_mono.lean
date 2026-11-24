-- Prove2me | Theorems.Thm_FongoSync_liveAt_mono
-- name    : FongoSync.liveAt_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:29.253797+00:00
-- url     : https://prove2.me/theorems/0c7d5ab9-e01c-4e53-bd1d-aec62d86dd7a
-- title:
--   Fongo Sync: live At mono
-- statement:
--   The Fongo Sync construction uses the live At mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L24-L28
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L24-L28

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveAt_mono {k j : Nat} (hkj : k ≤ j) {g : Gid} (h : liveAt sc inp k g) :
    liveAt sc inp j g := by sorry
