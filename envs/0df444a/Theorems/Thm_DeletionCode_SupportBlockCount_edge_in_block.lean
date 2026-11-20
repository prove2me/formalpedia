-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_edge_in_block
-- name    : DeletionCode.SupportBlockCount.edge_in_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:11.715922+00:00
-- url     : https://prove2.me/theorems/68ad3b8b-a43d-4516-9895-f95bacc8f753
-- title:
--   Support Block Count: edge in block
-- statement:
--   An edge touching an old block is an edge of that block's actual support.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L29-L37
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L29-L37

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.edge_in_block {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v)
    (hu : Incident B u) : RuleSetEdge B u v := by sorry
