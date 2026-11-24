-- Prove2me | Theorems.Thm_FongoSync_fold_apply_mem
-- name    : FongoSync.fold_apply_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:43.798101+00:00
-- url     : https://prove2.me/theorems/7ed8f835-1cdb-424c-8eed-e205f5054c3c
-- title:
--   Fongo Sync: fold apply mem
-- statement:
--   Whatever was given to a register, it holds one of those entries.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L330-L336
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L330-L336

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.fold_apply_mem (s : Strategy) (l : List (Entry V)) (m : Entry V)
    (h : l.foldl (apply s) none = some m) : m ∈ l := by sorry
