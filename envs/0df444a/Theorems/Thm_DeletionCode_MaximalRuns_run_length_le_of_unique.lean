-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_run_length_le_of_unique
-- name    : DeletionCode.MaximalRuns.run_length_le_of_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:31:11.805362+00:00
-- url     : https://prove2.me/theorems/c259485c-f58e-4e22-9b56-d4cc87a62a50
-- title:
--   Maximal Runs: run length le of unique
-- statement:
--   The source uniqueness bound applies to every displayed run decomposition.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L125-L133
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L125-L133

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.run_length_le_of_unique (word : List Bool) (k : ℕ)
    (hx : KUnique (listLetters word) word.length k)
    (pre suffix : List Bool) (rho : ℕ) (bit : Bool)
    (hword : word = pre ++ List.replicate rho bit ++ suffix) : rho ≤ k := by sorry
