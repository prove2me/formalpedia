-- Prove2me | solution 2 for finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:51.562429+00:00
-- url     : https://prove2.me/submissions/cfebcb66-4e87-405f-94c6-aec6fa3e3298

import Mathlib
import Theorems.Thm_finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K)
    (hcard : 2 ≤ Fintype.card V)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ (A : Set V), A.Nonempty → Aᶜ.Nonempty →
        (∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) →
        ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
          ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ H.Connected := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨H, hKH, hPH, hmax⟩ :=
    finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1 P K hK
  by_cases hconn : H.Connected
  · exact ⟨H, hKH, hPH, hconn⟩
  · obtain ⟨x⟩ := ‹Nonempty V›
    let A : Set V := {v | H.Reachable x v}
    have hA : A.Nonempty := ⟨x, by simp [A]⟩
    have hnotall : ¬ ∀ w, H.Reachable x w := by
      intro hall
      exact hconn ((SimpleGraph.connected_iff_exists_forall_reachable H).2 ⟨x, hall⟩)
    obtain ⟨y, hy⟩ := not_forall.mp hnotall
    have hAc : Aᶜ.Nonempty := ⟨y, by simp [A, hy]⟩
    have hno : ∀ u ∈ A, ∀ v ∉ A, ¬ H.Adj u v := by
      intro u hu v hv hadj
      apply hv
      change H.Reachable x v
      exact hu.trans hadj.reachable
    obtain ⟨J, hHJ, hPJ, u, v, hu, hv, hJuv⟩ := hbridge H hPH A hA hAc hno
    have hnot : ¬ H.Adj u v := hno u hu v hv
    have hlt : H < J := lt_of_le_of_ne hHJ (by
      intro heq
      subst J
      exact hnot hJuv)
    exact False.elim (hmax J (le_trans hKH hHJ) hPJ hlt)