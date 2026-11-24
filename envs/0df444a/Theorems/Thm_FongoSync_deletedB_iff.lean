-- Prove2me | Theorems.Thm_FongoSync_deletedB_iff
-- name    : FongoSync.deletedB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:50.641798+00:00
-- url     : https://prove2.me/theorems/218f045d-f91d-4f51-af36-a94de63dc511
-- title:
--   Fongo Sync: deleted B iff
-- statement:
--   The Fongo Sync construction uses the deleted B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L175-L177
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L175-L177

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.deletedB_iff (g : Gid) : deletedB sc inp g = true ↔ deleted sc inp g := by sorry
