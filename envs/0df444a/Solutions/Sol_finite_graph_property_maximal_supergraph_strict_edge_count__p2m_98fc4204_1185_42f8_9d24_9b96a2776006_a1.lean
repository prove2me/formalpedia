-- Prove2me | solution 1 for finite_graph_property_maximal_supergraph_strict_edge_count__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:05:32.117731+00:00
-- url     : https://prove2.me/submissions/8e3fb7af-4c03-4cac-8c66-5f627719fba6

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (H J : SimpleGraph V)
    (dH : DecidableRel H.Adj) (dJ : DecidableRel J.Adj)
    (hHJ : ∀ u v, H.Adj u v → J.Adj u v)
    (hstrict : ∃ u v, J.Adj u v ∧ ¬ H.Adj u v) :
    (letI : DecidableRel H.Adj := dH
     letI : DecidableRel J.Adj := dJ
     H.edgeFinset.card < J.edgeFinset.card) := by
  classical
  letI : DecidableRel H.Adj := dH
  letI : DecidableRel J.Adj := dJ
  apply Finset.card_lt_card
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
  apply lt_iff_le_not_ge.mpr
  constructor
  · exact hHJ
  · intro hJH
    obtain ⟨u, v, huvJ, huvH⟩ := hstrict
    exact huvH (hJH huvJ)