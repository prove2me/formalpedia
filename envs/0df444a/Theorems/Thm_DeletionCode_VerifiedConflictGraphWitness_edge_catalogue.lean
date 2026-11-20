-- Prove2me | Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_edge_catalogue
-- name    : DeletionCode.VerifiedConflictGraphWitness.edge_catalogue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:59:08.709282+00:00
-- url     : https://prove2.me/theorems/84a86ffa-4ffc-4845-badf-e592a5f95992
-- title:
--   Verified Conflict Graph Witness: edge catalogue
-- statement:
--   Every edge of the actual retained conflict graph is a catalogue rule;
--   coverage is proved internally.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L56-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L56-L59

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_catalogue

set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases

theorem DeletionCode.VerifiedConflictGraphWitness.edge_catalogue {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    ConnectedBlocks.CatalogueRule t k (spectrum k y.val - spectrum k x.val) := by sorry
