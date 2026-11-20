-- Prove2me | Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_edge_surviving
-- name    : DeletionCode.VerifiedConflictGraphWitness.edge_surviving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:59:34.451371+00:00
-- url     : https://prove2.me/theorems/f191de29-27d3-4e88-9fb7-c51a63d4a968
-- title:
--   Verified Conflict Graph Witness: edge surviving
-- statement:
--   The Verified Conflict Graph Witness construction uses the edge surviving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L61-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L61-L64

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Theorems.Thm_DeletionCode_ConflictGraphWitness_edge_surviving

set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases

theorem DeletionCode.VerifiedConflictGraphWitness.edge_surviving {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H := by sorry
