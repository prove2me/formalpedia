-- Prove2me | Theorems.Thm_FongoSync_fold_apply_dup
-- name    : FongoSync.fold_apply_dup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:52.122535+00:00
-- url     : https://prove2.me/theorems/7e7c2ff5-b9a6-4a6c-ab3d-5280ed848144
-- title:
--   Fongo Sync: fold apply dup
-- statement:
--   The Fongo Sync construction uses the fold apply dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L414-L416
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L414-L416

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.fold_apply_dup (s : Strategy) (l : List (Entry V)) (unique : UniqueClocks l) :
    (l ++ l).foldl (apply s) none = l.foldl (apply s) none := by sorry
