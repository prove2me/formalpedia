-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_eraseIdx_in_run
-- name    : DeletionCode.MaximalRuns.eraseIdx_in_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:57.181328+00:00
-- url     : https://prove2.me/theorems/1ee1e92a-9f82-46c5-b7fa-035abe1e638a
-- title:
--   Maximal Runs: erase Idx in run
-- statement:
--   Deleting anywhere in a constant run yields the same shortened list.
--   Maximality is not needed for this local edit identity.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L106-L115
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L106-L115

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.eraseIdx_in_run (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (pos : ℕ)
    (hstart : pre.length ≤ pos) (hstop : pos < pre.length + rho) :
    (pre ++ List.replicate rho bit ++ suffix).eraseIdx pos =
      pre ++ List.replicate (rho - 1) bit ++ suffix := by sorry
