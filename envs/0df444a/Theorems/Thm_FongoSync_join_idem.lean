-- Prove2me | Theorems.Thm_FongoSync_join_idem
-- name    : FongoSync.join_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:08.918025+00:00
-- url     : https://prove2.me/theorems/15c6539e-dca9-4df2-bf93-a59773d8b19e
-- title:
--   Fongo Sync: join idem
-- statement:
--   The Fongo Sync construction uses the join idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L95-L98
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L95-L98

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

theorem FongoSync.join_idem (a : Option E) : join cmp key a a = a := by sorry
