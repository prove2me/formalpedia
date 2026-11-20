-- Prove2me | Theorems.Thm_DeletionCode_OptimalRedundancy_optimalRedundancy_le_code
-- name    : DeletionCode.OptimalRedundancy.optimalRedundancy_le_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:12:20.574862+00:00
-- url     : https://prove2.me/theorems/48ebd423-cd1d-4b58-8ad7-9b5b18117723
-- title:
--   Optimal Redundancy: optimal Redundancy le code
-- statement:
--   The Optimal Redundancy construction uses the optimal Redundancy le code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L71-L79
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L71-L79

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter

theorem DeletionCode.OptimalRedundancy.optimalRedundancy_le_code (t n : ℕ) (C : Finset (Bits n))
    (hC : CodeSelection.Corrects t C) (hne : C.Nonempty) :
    optimalRedundancy t n ≤ RedundancyBounds.redundancy n C := by sorry
