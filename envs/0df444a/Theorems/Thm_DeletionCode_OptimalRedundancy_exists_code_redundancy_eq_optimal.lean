-- Prove2me | Theorems.Thm_DeletionCode_OptimalRedundancy_exists_code_redundancy_eq_optimal
-- name    : DeletionCode.OptimalRedundancy.exists_code_redundancy_eq_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:12:02.124568+00:00
-- url     : https://prove2.me/theorems/94ea72e8-8cd1-4107-806e-25847a1cabfb
-- title:
--   Optimal Redundancy: exists code redundancy eq optimal
-- statement:
--   The maximum-cardinality definition is exactly the minimum attainable redundancy.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L82-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L82-L87

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter

theorem DeletionCode.OptimalRedundancy.exists_code_redundancy_eq_optimal (t n : ℕ) :
    ∃ C : Finset (Bits n), CodeSelection.Corrects t C ∧ C.Nonempty ∧
      RedundancyBounds.redundancy n C = optimalRedundancy t n := by sorry
