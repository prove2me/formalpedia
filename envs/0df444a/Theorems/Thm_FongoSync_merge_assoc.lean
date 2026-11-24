-- Prove2me | Theorems.Thm_FongoSync_merge_assoc
-- name    : FongoSync.merge_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:13.600875+00:00
-- url     : https://prove2.me/theorems/9ea55819-f449-4854-8d63-5b889d6749d6
-- title:
--   Fongo Sync: merge assoc
-- statement:
--   The Fongo Sync construction uses the merge assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L391-L396
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L391-L396

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merge_assoc (s : Strategy) (a b c : Option (Entry V)) :
    merge s (merge s a b) c = merge s a (merge s b c) := by sorry
