-- Prove2me | solution 1 for empty_graph_component_count__p2m_32fb842e_c5cc_4fb3_a16d_c8f1f928ca75_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:28.293758+00:00
-- url     : https://prove2.me/submissions/5d7b0e84-171c-47cd-a45f-c5cd716324bb

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V] :
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Fintype.card V := by
  classical
  let e : (⊥ : SimpleGraph V).ConnectedComponent ≃ V :=
    { toFun := SimpleGraph.ConnectedComponent.lift id
        (by
          intro v w p hp
          exact SimpleGraph.reachable_bot.mp p.reachable)
      invFun := fun v => (⊥ : SimpleGraph V).connectedComponentMk v
      left_inv := by
        intro c
        refine SimpleGraph.ConnectedComponent.ind (G := (⊥ : SimpleGraph V)) ?_ c
        intro v
        simp
      right_inv := by
        intro v
        rfl }
  calc
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Nat.card V := Nat.card_congr e
    _ = Fintype.card V := Nat.card_eq_fintype_card