-- Prove2me | Theorems.Thm_FongoSync_apply_twice
-- name    : FongoSync.apply_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:00.501593+00:00
-- url     : https://prove2.me/theorems/d81c7da9-4aea-460c-a8f7-4ef12464f727
-- title:
--   Fongo Sync: apply twice
-- statement:
--   The Fongo Sync construction uses the apply twice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L343-L347
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L343-L347

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.apply_twice (s : Strategy) (h : Option (Entry V)) (e : Entry V) :
    apply s (apply s h e) e = apply s h e := by sorry
