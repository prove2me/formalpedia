-- Prove2me | solution 1 for simpleGraph_edgeSet_ncard_le_of_le__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:37:29.907185+00:00
-- url     : https://prove2.me/submissions/0f5765c7-39e2-420e-a3dd-ab5bb27f3e80

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hEdge : G.edgeSet ⊆ H.edgeSet)
    (N : Nat)
    (hBound : H.edgeSet.ncard ≤ N) :
    G.edgeSet.ncard ≤ N := by
  exact (Set.ncard_le_ncard hEdge (Set.toFinite _)).trans hBound