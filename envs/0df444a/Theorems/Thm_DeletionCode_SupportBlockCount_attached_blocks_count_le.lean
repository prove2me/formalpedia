-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_attached_blocks_count_le
-- name    : DeletionCode.SupportBlockCount.attached_blocks_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:05.738881+00:00
-- url     : https://prove2.me/theorems/8fe8675e-f02b-4d15-ab89-e156b19c308a
-- title:
--   Support Block Count: attached blocks count le
-- statement:
--   In particular, the actual collection of all blocks touching w has this bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L128-L137
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L128-L137

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.attached_blocks_count_le {t k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G) :
    (attachedBlocks G w).card ≤ 2 * t := by sorry
