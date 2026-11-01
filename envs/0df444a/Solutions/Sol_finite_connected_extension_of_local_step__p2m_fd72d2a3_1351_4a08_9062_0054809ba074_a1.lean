-- Prove2me | solution 1 for finite_connected_extension_of_local_step__p2m_fd72d2a3_1351_4a08_9062_0054809ba074_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:22.362914+00:00
-- url     : https://prove2.me/submissions/523a023b-984f-4549-9def-fbff353b9171

import Mathlib
import Theorems.Thm_finite_graph_predicate_maximal_extension__p2m_5e22ecc2_fcd1_4580_86fc_2603fce53c32_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hstep : ∀ (G : SimpleGraph V), K ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by
  obtain ⟨G, hKG, hPG, hmax⟩ :=
    finite_graph_predicate_maximal_extension__p2m_5e22ecc2_fcd1_4580_86fc_2603fce53c32_a1
      K P hK
  refine ⟨G, hKG, ?_, hPG⟩
  by_contra hGconn
  obtain ⟨H, hGH, hPH, u, v, hnotReach, hAdj⟩ := hstep G hKG hPG hGconn
  have hHG : H ≤ G := hmax H hGH hPH
  have hEq : H = G := le_antisymm hHG hGH
  subst H
  exact hnotReach hAdj.reachable