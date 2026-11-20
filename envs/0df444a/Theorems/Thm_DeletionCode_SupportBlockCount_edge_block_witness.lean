-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_edge_block_witness
-- name    : DeletionCode.SupportBlockCount.edge_block_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:56.096828+00:00
-- url     : https://prove2.me/theorems/efde0f34-5a9f-4c53-a270-732c06aa5bbb
-- title:
--   Support Block Count: edge block witness
-- statement:
--   An actual support edge lies entirely in the old block of its owning rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L17-L26
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L17-L26

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.edge_block_witness {k : ℕ} (G : RuleSet k)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v) :
    ∃ B ∈ blocks G, RuleSetEdge B u v ∧ Incident B u ∧ Incident B v := by sorry
