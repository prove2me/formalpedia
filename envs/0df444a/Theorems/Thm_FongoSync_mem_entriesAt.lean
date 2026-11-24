-- Prove2me | Theorems.Thm_FongoSync_mem_entriesAt
-- name    : FongoSync.mem_entriesAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:16.045926+00:00
-- url     : https://prove2.me/theorems/ef93d400-2d0e-47e7-b337-62beb4f879b1
-- title:
--   Fongo Sync: mem entries At
-- statement:
--   The Fongo Sync construction uses the mem entries At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L86-L88
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L86-L88

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
omit [Ord V]

theorem FongoSync.mem_entriesAt {cs : List (Change V)} {k : Key} {e : Entry V} :
    e ∈ entriesAt cs k ↔ ∃ c ∈ cs, c.key = k ∧ c.entry = e := by sorry
