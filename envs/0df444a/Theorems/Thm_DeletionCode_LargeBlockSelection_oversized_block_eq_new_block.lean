-- Prove2me | Theorems.Thm_DeletionCode_LargeBlockSelection_oversized_block_eq_new_block
-- name    : DeletionCode.LargeBlockSelection.oversized_block_eq_new_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:39.784171+00:00
-- url     : https://prove2.me/theorems/6d357df2-dc84-4079-b19c-60d081f8e598
-- title:
--   Large Block Selection: oversized block eq new block
-- statement:
--   If every old block has size at most L, an oversized new block must be the
--   block of the adjoined rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L73-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LargeBlockSelection.lean#L73-L82

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction

theorem DeletionCode.LargeBlockSelection.oversized_block_eq_new_block {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (B : RuleSet k) (hB : B ∈ blocks (insert w G)) (hlarge : L < B.card) :
    B = blockOf (insert w G) w := by sorry
