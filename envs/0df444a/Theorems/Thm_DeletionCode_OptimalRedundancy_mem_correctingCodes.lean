-- Prove2me | Theorems.Thm_DeletionCode_OptimalRedundancy_mem_correctingCodes
-- name    : DeletionCode.OptimalRedundancy.mem_correctingCodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:11:17.255321+00:00
-- url     : https://prove2.me/theorems/a1283fdc-0dd7-43a3-91ea-39ef0318d482
-- title:
--   Optimal Redundancy: mem correcting Codes
-- statement:
--   The Optimal Redundancy construction uses the mem correcting Codes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L19-L22
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L19-L22

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter

theorem DeletionCode.OptimalRedundancy.mem_correctingCodes (t n : ℕ) (C : Finset (Bits n)) :
    C ∈ correctingCodes t n ↔ CodeSelection.Corrects t C := by sorry
