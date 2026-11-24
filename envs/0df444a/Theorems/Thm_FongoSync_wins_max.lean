-- Prove2me | Theorems.Thm_FongoSync_wins_max
-- name    : FongoSync.wins_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:18.374802+00:00
-- url     : https://prove2.me/theorems/b3fcfbf4-e6da-447f-9afe-8d517a8e2a15
-- title:
--   Fongo Sync: wins max
-- statement:
--   The Fongo Sync construction uses the wins max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L311-L316
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L311-L316

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.wins_max (s : Entry V) (v : V) (c : Hlc) :
    wins .max (some s) v c = ((compare s.value v).then (compare s.clock c) == .lt) := by sorry
