-- Prove2me | Theorems.Thm_FongoSync_apply_max
-- name    : FongoSync.apply_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:56.841443+00:00
-- url     : https://prove2.me/theorems/ba312d84-2277-4904-97b9-36a3368970c1
-- title:
--   Fongo Sync: apply max
-- statement:
--   The Fongo Sync construction uses the apply max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L318-L324
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L318-L324

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.apply_max (held : Option (Entry V)) (e : Entry V) :
    apply .max held e = keep maxCmp Entry.pair held e := by sorry
