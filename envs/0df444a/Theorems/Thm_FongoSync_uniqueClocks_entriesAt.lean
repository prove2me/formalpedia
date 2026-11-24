-- Prove2me | Theorems.Thm_FongoSync_uniqueClocks_entriesAt
-- name    : FongoSync.uniqueClocks_entriesAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:31.739545+00:00
-- url     : https://prove2.me/theorems/a9777967-0e37-425f-9f82-1546319bf451
-- title:
--   Fongo Sync: unique Clocks entries At
-- statement:
--   The Fongo Sync construction uses the unique Clocks entries At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L90-L97
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L90-L97

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]

theorem FongoSync.uniqueClocks_entriesAt {cs : List (Change V)} (h : ClockDetermines cs) (k : Key) :
    UniqueClocks (entriesAt cs k) := by sorry
