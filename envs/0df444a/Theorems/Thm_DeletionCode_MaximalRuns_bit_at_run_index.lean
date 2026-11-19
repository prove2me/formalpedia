-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_bit_at_run_index
-- name    : DeletionCode.MaximalRuns.bit_at_run_index
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:31:04.789168+00:00
-- url     : https://prove2.me/theorems/827b7230-044f-4716-a9b6-9d8bc9e000bc
-- title:
--   Maximal Runs: bit at run index
-- statement:
--   The Maximal Runs construction uses the bit at run index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L97-L102
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L97-L102

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.bit_at_run_index (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (pos : ℕ)
    (hstart : pre.length ≤ pos) (hstop : pos < pre.length + rho) :
    listLetters (pre ++ List.replicate rho bit ++ suffix) pos = bit := by sorry
