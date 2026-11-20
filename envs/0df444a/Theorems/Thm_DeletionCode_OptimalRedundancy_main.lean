-- Prove2me | Theorems.Thm_DeletionCode_OptimalRedundancy_main
-- name    : DeletionCode.OptimalRedundancy.main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:55:26.556503+00:00
-- url     : https://prove2.me/theorems/51cd39b2-5ba2-4f7f-b2f4-cd83ec7980d2
-- title:
--   Optimal Redundancy: main
-- statement:
--   The manuscript's upper bound for optimal edit-correcting redundancy.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L90-L99
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L90-L99

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_CodeExistence_main

set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter

theorem DeletionCode.OptimalRedundancy.main (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      optimalRedundancy t n ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) := by sorry
