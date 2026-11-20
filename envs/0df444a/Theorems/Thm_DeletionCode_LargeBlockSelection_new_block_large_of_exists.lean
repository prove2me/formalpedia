-- Prove2me | Theorems.Thm_DeletionCode_LargeBlockSelection_new_block_large_of_exists
-- name    : DeletionCode.LargeBlockSelection.new_block_large_of_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:34.473351+00:00
-- url     : https://prove2.me/theorems/31555412-0447-4e66-af58-66c2ac0e9f7b
-- title:
--   Large Block Selection: new block large of exists
-- statement:
--   The stopping condition that some new block is too large gives the lower
--   bound on the specific new block used in the witness construction.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L86-L92
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L86-L92

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

theorem DeletionCode.LargeBlockSelection.new_block_large_of_exists {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (hlarge : ∃ B ∈ blocks (insert w G), L < B.card) :
    L < (blockOf (insert w G) w).card := by sorry
