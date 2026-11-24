-- Prove2me | Theorems.Thm_FongoSync_keep_idem
-- name    : FongoSync.keep_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:11.957625+00:00
-- url     : https://prove2.me/theorems/25a250d8-3013-47cf-8f3a-f587a09cad89
-- title:
--   Fongo Sync: keep idem
-- statement:
--   The Fongo Sync construction uses the keep idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L54-L60
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L54-L60

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

theorem FongoSync.keep_idem (h : Option E) (e : E) : keep cmp key (keep cmp key h e) e = keep cmp key h e := by sorry
