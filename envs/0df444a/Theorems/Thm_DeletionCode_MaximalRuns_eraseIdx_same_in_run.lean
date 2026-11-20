-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_eraseIdx_same_in_run
-- name    : DeletionCode.MaximalRuns.eraseIdx_same_in_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:47.876871+00:00
-- url     : https://prove2.me/theorems/42fdcb86-6ea8-4ab7-ae0f-e67c468674c2
-- title:
--   Maximal Runs: erase Idx same in run
-- statement:
--   The Maximal Runs construction uses the erase Idx same in run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L117-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L117-L122

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.eraseIdx_same_in_run (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (p q : ℕ)
    (hp : pre.length ≤ p) (hp' : p < pre.length + rho)
    (hq : pre.length ≤ q) (hq' : q < pre.length + rho) :
    (pre ++ List.replicate rho bit ++ suffix).eraseIdx p =
      (pre ++ List.replicate rho bit ++ suffix).eraseIdx q := by sorry
