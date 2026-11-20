-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_support_path_in_block
-- name    : DeletionCode.SupportBlockCount.support_path_in_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:14.869358+00:00
-- url     : https://prove2.me/theorems/c86670d2-3d24-4abc-8d3f-d8f0ce6a15ec
-- title:
--   Support Block Count: support path in block
-- statement:
--   The same actual support path can be restricted to the old block's edges.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L67-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L67-L84

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.support_path_in_block {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (hpath : RuleSetConnected G u v) :
    Incident B u → RuleSetConnected B u v := by sorry
