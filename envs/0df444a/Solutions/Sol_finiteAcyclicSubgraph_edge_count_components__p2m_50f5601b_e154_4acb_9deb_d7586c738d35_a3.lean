-- Prove2me | solution 1 for finiteAcyclicSubgraph_edge_count_components__p2m_50f5601b_e154_4acb_9deb_d7586c738d35_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:49.051672+00:00
-- url     : https://prove2.me/submissions/38df7481-a47e-4dfd-96d0-570e85164d46

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_acyclic_edgeSet_ncard_add_component_card__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a2
import Theorems.Thm_component_card_eq_of_reachable_iff__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a4

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (F K : SimpleGraph V) (hF : F.IsAcyclic)
    (hReach : ∀ u v, F.Reachable u v ↔ K.Reachable u v) :
    F.edgeSet.ncard + Nat.card K.ConnectedComponent = Fintype.card V := by
  have hcc : Nat.card F.ConnectedComponent = Nat.card K.ConnectedComponent :=
    component_card_eq_of_reachable_iff__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a4 F K hReach
  rw [← hcc]
  exact acyclic_edgeSet_ncard_add_component_card__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a2 F hF