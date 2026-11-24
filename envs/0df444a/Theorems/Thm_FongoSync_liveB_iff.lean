-- Prove2me | Theorems.Thm_FongoSync_liveB_iff
-- name    : FongoSync.liveB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:56.640238+00:00
-- url     : https://prove2.me/theorems/5cfeb2b3-5240-470e-b9cc-1c9eeb591b57
-- title:
--   Fongo Sync: live B iff
-- statement:
--   The Fongo Sync construction uses the live B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L191-L211
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L191-L211

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveB_iff (k : Nat) (g : Gid) : liveB sc inp k g = true ↔ liveAt sc inp k g := by sorry
