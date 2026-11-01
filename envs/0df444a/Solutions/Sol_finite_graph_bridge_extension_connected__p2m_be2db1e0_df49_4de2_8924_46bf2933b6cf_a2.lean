-- Prove2me | solution 1 for finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:02:01.527743+00:00
-- url     : https://prove2.me/submissions/cbf99834-b246-43b2-a8dd-b349f5f59b89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
import Theorems.Thm_disconnected_graph_has_cut__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
import Theorems.Thm_crossing_adjacency_makes_strict_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1

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
  obtain ⟨H, hKH, hPH, hmax⟩ :=
    finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1 P K hK
  by_cases hconn : H.Connected
  · exact ⟨H, hKH, hPH, hconn⟩
  · obtain ⟨A, hA, hAc, hno⟩ :=
      disconnected_graph_has_cut__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1 H hconn
    obtain ⟨J, hHJ, hPJ, u, v, hu, hv, hJuv⟩ := hbridge H hPH A hA hAc hno
    have hnot : ¬ H.Adj u v := hno u hu v hv
    have hlt : H < J :=
      crossing_adjacency_makes_strict_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
        H J hHJ u v hnot hJuv
    exact False.elim (hmax J (le_trans hKH hHJ) hPJ hlt)