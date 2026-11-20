-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_catalogue_block_count_le
-- name    : DeletionCode.SupportBlockCount.catalogue_block_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:52.947797+00:00
-- url     : https://prove2.me/theorems/ad8a7e54-6d7f-4481-99d6-30c81126ddfc
-- title:
--   Support Block Count: catalogue block count le
-- statement:
--   A catalogue rule with support inside G can meet at most 2t old blocks.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L118-L125
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L118-L125

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.catalogue_block_count_le {t k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (Bs : Finset (RuleSet k))
    (hw : CatalogueRule t k w) (hBs : Bs ⊆ blocks G)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G)
    (hhit : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v) :
    Bs.card ≤ 2 * t := by sorry
