-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_exists_insertion_run_at_gap_unique
-- name    : DeletionCode.MaximalRuns.exists_insertion_run_at_gap_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:34:16.379923+00:00
-- url     : https://prove2.me/theorems/1611c548-d20f-4da7-b7e9-d59e8762e32d
-- title:
--   Maximal Runs: exists insertion run at gap unique
-- statement:
--   Valid insertion gaps, including either boundary, have the same concrete
--   maximal-run decomposition and length bound without a supplied list split.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L196-L212
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L196-L212

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.exists_insertion_run_at_gap_unique (word : List Bool) (pos : ℕ) (bit : Bool)
    (k : ℕ) (hpos : pos ≤ word.length)
    (hx : KUnique (listLetters word) word.length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ),
      0 < rho ∧ rho ≤ k + 1 ∧
      word.take pos ++ bit :: word.drop pos = pre ++ List.replicate rho bit ++ suffix ∧
      word = pre ++ List.replicate (rho - 1) bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by sorry
