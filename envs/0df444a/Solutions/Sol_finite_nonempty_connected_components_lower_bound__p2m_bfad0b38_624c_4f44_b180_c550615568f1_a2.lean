-- Prove2me | solution 1 for finite_nonempty_connected_components_lower_bound__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
-- status  : ACCEPTED   (prove)
-- author  : @ishaan
-- created : 2026-11-10T00:17:37.735266+00:00
-- url     : https://prove2.me/submissions/e596e6f0-c8f7-46ae-918b-8901c5c4337e

import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

/-- A nonempty disconnected subspace with finitely many connected components
has at least two components. -/
theorem solution
    (X : Type) [TopologicalSpace X] (s : Set X)
    (hfinite : Finite (ConnectedComponents s)) (hne : s.Nonempty)
    (hdisconnected : ¬ IsConnected s) :
    2 ≤ Nat.card (ConnectedComponents s) := by
  classical
  let : Finite (ConnectedComponents s) := hfinite
  let : Nonempty s := hne.to_subtype
  by_contra h
  -- A nonempty space has at least one component. If there are fewer than
  -- two, there is therefore exactly one.
  have hpos : 0 < Nat.card (ConnectedComponents s) := Nat.card_pos
  have hlt : Nat.card (ConnectedComponents s) < 2 := lt_of_not_ge h
  have hone : Nat.card (ConnectedComponents s) = 1 :=
    Nat.le_antisymm (Nat.le_of_lt_succ hlt) hpos
  let : Subsingleton (ConnectedComponents s) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  -- With only one component, every point belongs to the component of a
  -- chosen point. That component is the entire subspace, so it is connected.
  apply hdisconnected
  apply isConnected_iff_connectedSpace.mpr
  apply connectedSpace_iff_connectedComponent.mpr
  obtain ⟨x, hx⟩ := hne
  refine ⟨⟨x, hx⟩, eq_univ_of_univ_subset ?_⟩
  intro y _
  exact ConnectedComponents.coe_eq_coe'.mp
    (Subsingleton.elim (ConnectedComponents.mk y)
      (ConnectedComponents.mk (⟨x, hx⟩ : s)))
