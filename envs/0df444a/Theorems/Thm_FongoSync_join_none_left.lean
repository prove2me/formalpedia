-- Prove2me | Theorems.Thm_FongoSync_join_none_left
-- name    : FongoSync.join_none_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:13.196445+00:00
-- url     : https://prove2.me/theorems/15637e69-a3c3-49c5-8fdd-d6d4c8fd838b
-- title:
--   Fongo Sync: join none left
-- statement:
--   The Fongo Sync construction uses the join none left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L127-L128
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L127-L128

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}

theorem FongoSync.join_none_left (b : Option E) : join cmp key none b = b := by sorry
