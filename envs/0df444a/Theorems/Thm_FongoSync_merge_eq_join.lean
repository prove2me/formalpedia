-- Prove2me | Theorems.Thm_FongoSync_merge_eq_join
-- name    : FongoSync.merge_eq_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:23.607293+00:00
-- url     : https://prove2.me/theorems/96900f49-11f3-4697-9a3e-380ffe3ef556
-- title:
--   Fongo Sync: merge eq join
-- statement:
--   The Fongo Sync construction uses the merge eq join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L374-L378
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L374-L378

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merge_eq_join (s : Strategy) (a b : Option (Entry V)) :
    merge s a b = match s with
      | .lww => join compare Entry.clock a b
      | .max => join maxCmp Entry.pair a b := by sorry
