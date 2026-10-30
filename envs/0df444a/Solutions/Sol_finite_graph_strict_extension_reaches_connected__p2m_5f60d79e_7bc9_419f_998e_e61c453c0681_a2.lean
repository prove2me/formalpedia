-- Prove2me | solution 1 for finite_graph_strict_extension_reaches_connected__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:17.025875+00:00
-- url     : https://prove2.me/submissions/ca1d76e7-cb31-49b0-ad67-9405259a97b7

import Mathlib
import Theorems.Thm_exists_edge_maximal_property_extension__p2m_3d85fc57_8a7f_4a4a_b28a_c7b875c3ae9f_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hP : P H)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G.edgeSet ⊂ K.edgeSet ∧ P K) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ P K := by
  obtain ⟨K, hHK, hPK, hmax⟩ :=
    exists_edge_maximal_property_extension__p2m_3d85fc57_8a7f_4a4a_b28a_c7b875c3ae9f_a1 P H hP
  have hconn : K.Connected := by
    by_contra hnc
    obtain ⟨L, hKL, hPL⟩ := hstep K hPK hnc
    exact hmax L hKL hPL
  exact ⟨K, hHK, hconn, hPK⟩