-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_exists_head_run
-- name    : DeletionCode.MaximalRuns.exists_head_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:31:02.439577+00:00
-- url     : https://prove2.me/theorems/ab93ce35-1622-4f4e-bec4-f249c6a289dd
-- title:
--   Maximal Runs: exists head run
-- statement:
--   The first bit begins a nonempty run ending at the first opposite bit or
--   at the word's end. The run and its boundary are derived by list induction.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L20-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L20-L34

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.exists_head_run (bit : Bool) (tail : List Bool) :
    ∃ (rho : ℕ) (suffix : List Bool), 0 < rho ∧
      bit :: tail = List.replicate rho bit ++ suffix ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by sorry
