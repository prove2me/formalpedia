-- Prove2me | Theorems.Thm_DeletionCode_WordGraphWitness_component_witness
-- name    : DeletionCode.WordGraphWitness.component_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:34:14.828611+00:00
-- url     : https://prove2.me/theorems/e0f7ffe4-f604-40dc-a75e-6e9273d743dc
-- title:
--   Word Graph Witness: component witness
-- statement:
--   A nonbipartite component of a graph of k-unique words contains a bounded
--   surviving generating witness at every chosen word in that component.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordGraphWitness.lean#L17-L40
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordGraphWitness.lean#L17-L40

import Definitions.Def_DeletionCode_OddGraphWalk
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Definitions.Def_DeletionCode_WordGraphWitness
set_option autoImplicit true
open DeletionCode DeletionCode.WordGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks WitnessCases

theorem DeletionCode.WordGraphWitness.component_witness {V : Type*} {t k n : ℕ} (ht : 2 ≤ t)
    (G : SimpleGraph V) (words : V → Letters)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ v, KUnique (words v) n k)
    (hcat : ∀ {v w}, G.Adj v w → CatalogueRule t k
      (wordSpectrum (words w) n (windowLength k) -
        wordSpectrum (words v) n (windowLength k)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (words w) n (windowLength k) -
        wordSpectrum (words v) n (windowLength k)) ∈ K)
    (x : V) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (words x) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (words x) n k U.card (componentCount U) U := by sorry
