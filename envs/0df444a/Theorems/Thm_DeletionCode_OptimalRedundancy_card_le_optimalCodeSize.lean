-- Prove2me | Theorems.Thm_DeletionCode_OptimalRedundancy_card_le_optimalCodeSize
-- name    : DeletionCode.OptimalRedundancy.card_le_optimalCodeSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:11:51.989458+00:00
-- url     : https://prove2.me/theorems/f419fd20-81e9-47db-8b74-b1b1f0bbacd7
-- title:
--   Optimal Redundancy: card le optimal Code Size
-- statement:
--   The Optimal Redundancy construction uses the card le optimal Code Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L41-L44
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OptimalRedundancy.lean#L41-L44

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter

theorem DeletionCode.OptimalRedundancy.card_le_optimalCodeSize (t n : ℕ) (C : Finset (Bits n))
    (hC : CodeSelection.Corrects t C) : C.card ≤ optimalCodeSize t n := by sorry
