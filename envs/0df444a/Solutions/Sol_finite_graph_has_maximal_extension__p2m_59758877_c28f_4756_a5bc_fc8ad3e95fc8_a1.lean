-- Prove2me | solution 1 for finite_graph_has_maximal_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:04:47.827837+00:00
-- url     : https://prove2.me/submissions/b84f75d0-bb75-45cc-b61d-ee2428232b98

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ G : SimpleGraph V, K ≤ G → P G → ¬ H < G := by
  classical
  let admissible : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  have hK_admissible : admissible K := ⟨le_rfl, hK⟩
  obtain ⟨H, hKH, hmax⟩ := Finite.exists_le_maximal hK_admissible
  refine ⟨H, hKH, hmax.1.2, ?_⟩
  intro G hKG hPG hHG
  have hGH : G ≤ H := hmax.2 ⟨hKG, hPG⟩ hHG.1
  exact hHG.2 hGH