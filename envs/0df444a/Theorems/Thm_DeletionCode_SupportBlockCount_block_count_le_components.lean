-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_block_count_le_components
-- name    : DeletionCode.SupportBlockCount.block_count_le_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:53.190181+00:00
-- url     : https://prove2.me/theorems/fc11b4b9-7af4-45fc-9ef9-0da1a60c3c46
-- title:
--   Support Block Count: block count le components
-- statement:
--   Distinct old blocks met by w use distinct actual support components of w.
--   Both the map and its injectivity are derived from the given hit vertices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L88-L115
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L88-L115

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.block_count_le_components {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (Bs : Finset (RuleSet k))
    (hBs : Bs ⊆ blocks G)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G)
    (hhit : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v) :
    Bs.card ≤ componentCount {w} := by sorry
