-- Prove2me | solution 1 for simpleGraph_extension_card_le_reverse__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:15.615628+00:00
-- url     : https://prove2.me/submissions/d80cd21e-32ec-4ce7-a7c4-ae0fb256906e

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H G : SimpleGraph V)
    (hHG : H ≤ G)
    (hcard :
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel G.Adj := Classical.decRel G.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card)) : G ≤ H := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hsubset : H.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hHG he
  have heq : H.edgeFinset = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  rw [SimpleGraph.le_iff_adj]
  intro v w hvw
  have hmem : s(v, w) ∈ G.edgeFinset := by
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hvw]
  have hmemH : s(v, w) ∈ H.edgeFinset := by
    rw [heq]
    exact hmem
  simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmemH