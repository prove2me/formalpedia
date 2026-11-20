-- Prove2me | Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_surviving
-- name    : DeletionCode.ConflictGraphWitness.edge_surviving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:38:13.498109+00:00
-- url     : https://prove2.me/theorems/634c99c1-4a4a-411a-8f26-080d5d00c844
-- title:
--   Conflict Graph Witness: edge surviving
-- statement:
--   Equal circle bins imply actual hash survival for each catalogue edge.
--   Neither survival nor a norm estimate is assumed of graph edges.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConflictGraphWitness.lean#L59-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConflictGraphWitness.lean#L59-L64

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_WordGraphWitness
import Definitions.Def_DeletionCode_CircleHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
set_option autoImplicit true
open DeletionCode DeletionCode.ConflictGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks AlignmentTrace WitnessCases

theorem DeletionCode.ConflictGraphWitness.edge_surviving {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) (hcoverage : SeparatedCoverage t k n)
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H := by sorry
