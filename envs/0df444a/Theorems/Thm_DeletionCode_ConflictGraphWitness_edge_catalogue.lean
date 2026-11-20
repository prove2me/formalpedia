-- Prove2me | Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_catalogue
-- name    : DeletionCode.ConflictGraphWitness.edge_catalogue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:48.782959+00:00
-- url     : https://prove2.me/theorems/ef33bc80-1a06-4ce8-9a43-c7df315ec92c
-- title:
--   Conflict Graph Witness: edge catalogue
-- statement:
--   Exclusion of the explicit exceptional set supplies every input to
--   separated coverage. Catalogue membership is not an edge assumption.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConflictGraphWitness.lean#L50-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConflictGraphWitness.lean#L50-L55

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_WordGraphWitness
import Definitions.Def_DeletionCode_CircleHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
set_option autoImplicit true
open DeletionCode DeletionCode.ConflictGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks AlignmentTrace WitnessCases

theorem DeletionCode.ConflictGraphWitness.edge_catalogue {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hcoverage : SeparatedCoverage t k n)
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    CatalogueRule t k (spectrum k y.val - spectrum k x.val) := by sorry
