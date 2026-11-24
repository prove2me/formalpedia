-- Prove2me | Theorems.Thm_FongoSync_merge_idem
-- name    : FongoSync.merge_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:12.420133+00:00
-- url     : https://prove2.me/theorems/e64eefbc-97c8-4fca-9bc5-5a8c4538b4de
-- title:
--   Fongo Sync: merge idem
-- statement:
--   The Fongo Sync construction uses the merge idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L380-L381
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L380-L381

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merge_idem (s : Strategy) (a : Option (Entry V)) : merge s a a = a := by sorry
