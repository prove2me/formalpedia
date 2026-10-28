-- Prove2me | solution 1 for simpleGraph_eq_of_edge_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:25.696925+00:00
-- url     : https://prove2.me/submissions/1481dd1f-2e60-402d-8754-82760beb7e49

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    {G H : SimpleGraph V}
    (hGH : ∀ u v, G.Adj u v → H.Adj u v)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    G = H := by
  have hle : G ≤ H := fun u v h => hGH u v h
  have hs : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hle
  exact SimpleGraph.edgeSet_injective (Set.eq_of_subset_of_ncard_le hs hcard (Set.toFinite _))
