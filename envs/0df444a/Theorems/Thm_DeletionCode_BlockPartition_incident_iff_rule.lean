-- Prove2me | Theorems.Thm_DeletionCode_BlockPartition_incident_iff_rule
-- name    : DeletionCode.BlockPartition.incident_iff_rule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:05.274738+00:00
-- url     : https://prove2.me/theorems/abbff38f-248b-4bf5-9eb9-bfe0fbe72b32
-- title:
--   Block Partition: incident iff rule
-- statement:
--   Every incident vertex of a support union belongs to an actual rule in it.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L59-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockPartition.lean#L59-L68

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks

theorem DeletionCode.BlockPartition.incident_iff_rule {k : ℕ} (U : RuleSet k)
    (v : SupportComponents.Vertex (windowLength k)) :
    Incident U v ↔ ∃ w ∈ U, Incident {w} v := by sorry
