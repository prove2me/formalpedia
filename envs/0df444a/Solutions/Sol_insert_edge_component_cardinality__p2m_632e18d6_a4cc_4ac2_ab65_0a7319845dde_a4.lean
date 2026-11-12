-- Prove2me | solution 1 for insert_edge_component_cardinality__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a4
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T14:41:27.403488+00:00
-- url     : https://prove2.me/submissions/c1877aa4-f148-4082-986a-ad71dbe5fe71

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-- Adding an edge between two unreachable vertices merges exactly the two components, so the
remaining components are in bijection with the components of the enlarged graph. -/
theorem solution {V : Type} [Fintype V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hnreach : ¬ K.Reachable u v) :
    Nat.card {D : K.ConnectedComponent // D ≠ K.connectedComponentMk v} =
      Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent := by
  classical
  let K' : SimpleGraph V := K ⊔ SimpleGraph.edge u v
  have hK' : K' = K ⊔ SimpleGraph.edge u v := rfl
  let φ : K.ConnectedComponent → K'.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE le_sup_left)
  have hφmk : ∀ w : V, φ (K.connectedComponentMk w) = K'.connectedComponentMk w := by
    intro w
    simp [φ]
  -- Reachability in `K'` is ordinary `K`-reachability or one crossing of the new edge.
  have hchar : ∀ a b : V, K'.Reachable a b →
      K.Reachable a b ∨ (K.Reachable a u ∧ K.Reachable v b) ∨
        (K.Reachable a v ∧ K.Reachable u b) := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
    | cons hstep prest ih =>
      rw [hK', SimpleGraph.sup_adj] at hstep
      rcases hstep with hK | hedge
      · rcases ih with h | ⟨hcu, hvb⟩ | ⟨hcv, hub⟩
        · exact Or.inl (hK.reachable.trans h)
        · exact Or.inr (Or.inl ⟨hK.reachable.trans hcu, hvb⟩)
        · exact Or.inr (Or.inr ⟨hK.reachable.trans hcv, hub⟩)
      · rw [SimpleGraph.edge_adj] at hedge
        obtain ⟨hcase, -⟩ := hedge
        rcases hcase with ⟨hx, hc⟩ | ⟨hx, hc⟩
        · rw [hc] at ih
          rw [hx] at ⊢
          rcases ih with h | ⟨-, hvb⟩ | ⟨-, hub⟩
          · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl u, h⟩)
          · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl u, hvb⟩)
          · exact Or.inl hub
        · rw [hc] at ih
          rw [hx] at ⊢
          rcases ih with h | ⟨-, hvb⟩ | ⟨-, hub⟩
          · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl v, h⟩)
          · exact Or.inl hvb
          · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl v, hub⟩)
  let ψ : {D : K.ConnectedComponent // D ≠ K.connectedComponentMk v} →
      K'.ConnectedComponent := fun D => φ D.1
  have hψ_inj : Function.Injective ψ := by
    intro D1 D2 h
    apply Subtype.ext
    obtain ⟨w1, hw1⟩ := D1.1.exists_rep
    obtain ⟨w2, hw2⟩ := D2.1.exists_rep
    have hmk1 : φ D1.1 = K'.connectedComponentMk w1 := by rw [← hw1]; exact hφmk w1
    have hmk2 : φ D2.1 = K'.connectedComponentMk w2 := by rw [← hw2]; exact hφmk w2
    have hreach' : K'.Reachable w1 w2 := by
      rw [← SimpleGraph.ConnectedComponent.eq, ← hmk1, ← hmk2]
      exact h
    rcases hchar w1 w2 hreach' with hK | ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [← hw1, ← hw2]
      exact SimpleGraph.ConnectedComponent.sound hK
    · exfalso
      exact D2.2 (by rw [← hw2]; exact (SimpleGraph.ConnectedComponent.sound h2).symm)
    · exfalso
      exact D1.2 (by rw [← hw1]; exact SimpleGraph.ConnectedComponent.sound h1)
  have hψ_surj : Function.Surjective ψ := by
    intro C'
    obtain ⟨w, hw⟩ := C'.exists_rep
    by_cases hwv : K.connectedComponentMk w = K.connectedComponentMk v
    · refine ⟨⟨K.connectedComponentMk u, ?_⟩, ?_⟩
      · intro hu
        exact hnreach (SimpleGraph.ConnectedComponent.exact hu)
      · show φ (K.connectedComponentMk u) = C'
        rw [hφmk u, ← hw]
        apply SimpleGraph.ConnectedComponent.sound
        have hst : K'.Adj u v := by
          rw [hK', SimpleGraph.sup_adj]
          right
          rw [SimpleGraph.edge_adj]
          exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
        have htw : K'.Reachable v w :=
          SimpleGraph.Reachable.mono le_sup_left
            (SimpleGraph.ConnectedComponent.exact hwv.symm)
        exact hst.reachable.trans htw
    · refine ⟨⟨K.connectedComponentMk w, hwv⟩, ?_⟩
      show φ (K.connectedComponentMk w) = C'
      rw [hφmk w]
      exact hw
  exact Nat.card_congr (Equiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩)
