-- Prove2me | Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_bounded_witness
-- name    : DeletionCode.VerifiedConflictGraphWitness.bounded_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:59:57.495448+00:00
-- url     : https://prove2.me/theorems/23dcb8bf-a7b8-4b5c-b1bd-164e34f5153f
-- title:
--   Verified Conflict Graph Witness: bounded witness
-- statement:
--   The manuscript's complete deterministic bounded-witness lemma on the
--   actual finite conflict graph, with its explicit exceptional set and hash.
--   No earlier coverage lemma is left as an assumption.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L69-L75
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L69-L75

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases

theorem DeletionCode.VerifiedConflictGraphWitness.bounded_witness {t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x : Vertex (n := n) t Q H)
    (hnot : ¬ ((graph t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (spectrum k x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U := by sorry
