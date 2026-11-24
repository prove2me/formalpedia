-- Prove2me | Theorems.Thm_FongoSync_liveNow_iff
-- name    : FongoSync.liveNow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:45.871736+00:00
-- url     : https://prove2.me/theorems/6284727f-d00a-443b-a194-f3cd4ba515f1
-- title:
--   Fongo Sync: live Now iff
-- statement:
--   The Fongo Sync construction uses the live Now iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L216-L217
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L216-L217

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveNow_iff (g : Gid) : liveNow sc inp g = true ↔ Live sc inp g := by sorry
