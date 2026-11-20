-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_exists_maximal_run
-- name    : DeletionCode.MaximalRuns.exists_maximal_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:52.873817+00:00
-- url     : https://prove2.me/theorems/7f076643-bfa3-4932-a26d-1de1efcb15ae
-- title:
--   Maximal Runs: exists maximal run
-- statement:
--   A valid index lies in a concrete maximal run. Empty exterior words
--   represent runs reaching a boundary; otherwise the adjacent bit is opposite.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L38-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L38-L82

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.exists_maximal_run (word : List Bool) (pos : ℕ) (hpos : pos < word.length) :
    ∃ (pre suffix : List Bool) (rho : ℕ) (bit : Bool),
      0 < rho ∧ word = pre ++ List.replicate rho bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by sorry
