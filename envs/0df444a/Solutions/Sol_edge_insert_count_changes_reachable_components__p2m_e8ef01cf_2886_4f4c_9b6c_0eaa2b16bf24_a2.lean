-- Prove2me | solution 1 for edge_insert_count_changes_reachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:42:27.783043+00:00
-- url     : https://prove2.me/submissions/46645de8-4531-4b94-9bb3-906f0911577b

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false
open SimpleGraph

theorem inserted_adj_reachable {V : Type} (K : SimpleGraph V) (u v : V)
    (hreach : K.Reachable u v) :
    ∀ x y, (K ⊔ SimpleGraph.edge u v).Adj x y → K.Reachable x y := by
  intro x y h
  rcases (SimpleGraph.sup_adj K (SimpleGraph.edge u v) x y).mp h with hK | hE
  · exact hK.reachable
  · rcases ((SimpleGraph.edge_adj u v x y).mp hE).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hreach
    · exact hreach.symm

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hreach : K.Reachable u v) :
    Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent =
      Nat.card K.ConnectedComponent := by
  have hReach : ∀ x y, (K ⊔ SimpleGraph.edge u v).Reachable x y ↔ K.Reachable x y := by
    intro x y
    constructor
    · intro hxy
      have hclosure := Relation.reflTransGen_le_of_equivalence_of_le K.reachable_is_equivalence
        (inserted_adj_reachable K u v hreach)
      exact hclosure x y (((K ⊔ SimpleGraph.edge u v).reachable_iff_reflTransGen x y).mp hxy)
    · intro hxy
      exact hxy.mono le_sup_left
  exact Nat.card_congr (Quot.congr (Equiv.refl V) hReach)

