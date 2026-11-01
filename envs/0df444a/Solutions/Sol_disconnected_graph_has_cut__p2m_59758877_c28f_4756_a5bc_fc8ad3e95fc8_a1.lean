-- Prove2me | solution 1 for disconnected_graph_has_cut__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:04:45.859204+00:00
-- url     : https://prove2.me/submissions/c6adf781-55b7-4d30-90f7-ea6296faeef8

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        ¬ G.Connected →
          ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
            ∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) := by
  intro h
  let G : SimpleGraph Empty := ⊥
  have hG : ¬ G.Connected := by
    simp [G, SimpleGraph.connected_iff]
  obtain ⟨A, hA, hAc, hcross⟩ := h G hG
  rcases hA with ⟨x, hx⟩
  cases x