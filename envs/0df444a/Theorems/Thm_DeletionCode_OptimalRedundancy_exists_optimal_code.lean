-- Prove2me | Theorems.Thm_DeletionCode_OptimalRedundancy_exists_optimal_code
-- name    : DeletionCode.OptimalRedundancy.exists_optimal_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:11:24.581286+00:00
-- url     : https://prove2.me/theorems/b53307f8-0cbd-4e51-9632-cc2d1cac8bd9
-- title:
--   Optimal Redundancy: exists optimal code
-- statement:
--   Finiteness gives a correcting code attaining the maximum.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L56-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L56-L65

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter

theorem DeletionCode.OptimalRedundancy.exists_optimal_code (t n : ℕ) :
    ∃ C : Finset (Bits n), CodeSelection.Corrects t C ∧ C.Nonempty ∧
      C.card = optimalCodeSize t n := by sorry
