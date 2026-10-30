-- Prove2me | solution 1 for edge_insert_count_changes_edge_card__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:10.725683+00:00
-- url     : https://prove2.me/submissions/dfc9f7a9-cfb6-4baa-9b67-a6b8db43f886

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hnot : ¬ K.Adj u v) :
    K.edgeSet.ncard + 1 = (K ⊔ SimpleGraph.edge u v).edgeSet.ncard := by
  classical
  have hdisj : Disjoint K.edgeSet (SimpleGraph.edge u v).edgeSet := by
    rw [SimpleGraph.edgeSet_edge_of_ne hne]
    rw [Set.disjoint_left]
    intro e he hmem
    simp only [Set.mem_singleton_iff] at hmem
    subst e
    exact hnot (K.mem_edgeSet.mp he)
  rw [SimpleGraph.edgeSet_sup, Set.ncard_union_eq hdisj,
    SimpleGraph.edgeSet_edge_of_ne hne]
  simp