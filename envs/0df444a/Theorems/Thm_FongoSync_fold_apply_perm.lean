-- Prove2me | Theorems.Thm_FongoSync_fold_apply_perm
-- name    : FongoSync.fold_apply_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:48.531402+00:00
-- url     : https://prove2.me/theorems/b2cdb923-2097-4bbc-991d-4846c545c66a
-- title:
--   Fongo Sync: fold apply perm
-- statement:
--   The Fongo Sync construction uses the fold apply perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L409-L412
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L409-L412

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.fold_apply_perm (s : Strategy) {l₁ l₂ : List (Entry V)} (p : l₁.Perm l₂)
    (unique : UniqueClocks l₁) (h : Option (Entry V)) :
    l₁.foldl (apply s) h = l₂.foldl (apply s) h := by sorry
