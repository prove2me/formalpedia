-- Prove2me | Theorems.Thm_DeletionCode_WordGraphWitness_finite_word_component_witness
-- name    : DeletionCode.WordGraphWitness.finite_word_component_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:34:26.630875+00:00
-- url     : https://prove2.me/theorems/978c9bbc-b7c9-40f8-a0a6-e9f7986daeeb
-- title:
--   Word Graph Witness: finite word component witness
-- statement:
--   An actual finite-word graph is a direct specialization. Padding is fixed;
--   no unused infinite letter-function data is part of the graph's vertices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordGraphWitness.lean#L44-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordGraphWitness.lean#L44-L59

import Definitions.Def_DeletionCode_OddGraphWalk
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Definitions.Def_DeletionCode_WordGraphWitness
set_option autoImplicit true
open DeletionCode DeletionCode.WordGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks WitnessCases

theorem DeletionCode.WordGraphWitness.finite_word_component_witness {t k n : ℕ} (ht : 2 ≤ t)
    (vertices : Set (Bits n)) (G : SimpleGraph vertices)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ v ∈ vertices, KUnique (padBits v) n k)
    (hcat : ∀ {v w}, G.Adj v w → CatalogueRule t k
      (wordSpectrum (padBits w.val) n (windowLength k) -
        wordSpectrum (padBits v.val) n (windowLength k)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (padBits w.val) n (windowLength k) -
        wordSpectrum (padBits v.val) n (windowLength k)) ∈ K)
    (x : vertices) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (padBits x.val) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U := by sorry
