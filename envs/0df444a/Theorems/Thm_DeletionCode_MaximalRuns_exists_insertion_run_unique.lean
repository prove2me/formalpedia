-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_exists_insertion_run_unique
-- name    : DeletionCode.MaximalRuns.exists_insertion_run_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:33:51.906901+00:00
-- url     : https://prove2.me/theorems/c355da5c-0838-48fb-a64e-2707d6be6f26
-- title:
--   Maximal Runs: exists insertion run unique
-- statement:
--   For a k-unique source, the longer run produced by insertion has length
--   between one and k+1. Its shorter run may be empty, as when rho=1.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L170-L192
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L170-L192

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.exists_insertion_run_unique (left right : List Bool) (bit : Bool) (k : ℕ)
    (hx : KUnique (listLetters (left ++ right)) (left ++ right).length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ rho ≤ k + 1 ∧
      left ++ bit :: right = pre ++ List.replicate rho bit ++ suffix ∧
      left ++ right = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ left.length ∧ left.length < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by sorry
