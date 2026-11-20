-- Prove2me | Theorems.Thm_DeletionCode_SupportBlockCount_support_path_incident_iff
-- name    : DeletionCode.SupportBlockCount.support_path_incident_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:08.094692+00:00
-- url     : https://prove2.me/theorems/20b5cefd-be32-464d-aa5f-014e4840071e
-- title:
--   Support Block Count: support path incident iff
-- statement:
--   A support path in G cannot leave the incident vertices of its starting block.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L57-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportBlockCount.lean#L57-L64

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents

theorem DeletionCode.SupportBlockCount.support_path_incident_iff {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (hpath : RuleSetConnected G u v) :
    Incident B u ↔ Incident B v := by sorry
