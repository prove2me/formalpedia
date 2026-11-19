-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_exists_insertion_run
-- name    : DeletionCode.MaximalRuns.exists_insertion_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:33:50.359905+00:00
-- url     : https://prove2.me/theorems/29ac7da0-0e2f-44dc-87d6-f78e5b76e2d9
-- title:
--   Maximal Runs: exists insertion run
-- statement:
--   Inserting a bit into an actual list split yields a maximal run containing
--   that inserted bit. Shortening the extracted run recovers the exact source.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L151-L166
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L151-L166

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.exists_insertion_run (left right : List Bool) (bit : Bool) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ left ++ bit :: right = pre ++ List.replicate rho bit ++ suffix ∧
      left ++ right = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ left.length ∧ left.length < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by sorry
