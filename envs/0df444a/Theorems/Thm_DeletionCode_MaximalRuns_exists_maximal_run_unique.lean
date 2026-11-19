-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_exists_maximal_run_unique
-- name    : DeletionCode.MaximalRuns.exists_maximal_run_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:31:12.840183+00:00
-- url     : https://prove2.me/theorems/18b9e6e3-92d3-499f-8b7e-0dd20795a279
-- title:
--   Maximal Runs: exists maximal run unique
-- statement:
--   Extracting a maximal source run also derives its length bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L136-L147
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L136-L147

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.exists_maximal_run_unique (word : List Bool) (pos k : ℕ)
    (hpos : pos < word.length) (hx : KUnique (listLetters word) word.length k) :
    ∃ (pre suffix : List Bool) (rho : ℕ) (bit : Bool),
      0 < rho ∧ rho ≤ k ∧ word = pre ++ List.replicate rho bit ++ suffix ∧
      pre.length ≤ pos ∧ pos < pre.length + rho ∧
      (pre = [] ∨ pre.getLast? = some (!bit)) ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by sorry
