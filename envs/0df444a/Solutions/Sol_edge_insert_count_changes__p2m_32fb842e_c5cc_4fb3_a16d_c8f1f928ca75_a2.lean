-- Prove2me | solution 1 for edge_insert_count_changes__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:30.998055+00:00
-- url     : https://prove2.me/submissions/d24d4c19-b256-423d-bc38-c4699aa5c8da

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_edge_insert_count_changes_edge_card__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
import Theorems.Thm_edge_insert_count_changes_reachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
import Theorems.Thm_edge_insert_count_changes_unreachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V) (hKG : K ≤ G)
    (u v : V) (huv : u < v) (hadj : G.Adj u v) (hnot : ¬ K.Adj u v) :
    K.edgeSet.ncard + 1 = (K ⊔ SimpleGraph.edge u v).edgeSet.ncard ∧
    (∀ hreach : K.Reachable u v,
      Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent =
        Nat.card K.ConnectedComponent) ∧
    (∀ hnreach : ¬ K.Reachable u v,
      Nat.card K.ConnectedComponent =
        Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact edge_insert_count_changes_edge_card__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
      K u v (ne_of_lt huv) hnot
  · intro hreach
    exact edge_insert_count_changes_reachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
      K u v (ne_of_lt huv) hreach
  · intro hnreach
    exact edge_insert_count_changes_unreachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
      K u v (ne_of_lt huv) hnreach