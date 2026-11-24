-- Prove2me | Theorems.Thm_FongoSync_mem_of_liveAt
-- name    : FongoSync.mem_of_liveAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:04:34.981791+00:00
-- url     : https://prove2.me/theorems/19106dc6-e38c-48e6-9e61-77f423dabea7
-- title:
--   Fongo Sync: mem of live At
-- statement:
--   The Fongo Sync construction uses the mem of live At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L30-L36
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L30-L36

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.mem_of_liveAt {k : Nat} {g : Gid} (h : liveAt sc inp k g) : g ∈ inp.gids := by sorry
