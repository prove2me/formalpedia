-- Prove2me | Theorems.Thm_FongoSync_liveAt_succ_of
-- name    : FongoSync.liveAt_succ_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:41.541683+00:00
-- url     : https://prove2.me/theorems/28a5f051-696e-4ed2-9ee1-7bca303eea4e
-- title:
--   Fongo Sync: live At succ of
-- statement:
--   The Fongo Sync construction uses the live At succ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L21-L22
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L21-L22

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveAt_succ_of {k : Nat} {g : Gid} (h : liveAt sc inp k g) : liveAt sc inp (k + 1) g := by sorry
