-- Prove2me | solution 1 for finite_graph_property_has_maximal_extension__p2m_655608fd_9cc4_4697_9d54_637a0388a99e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:38.9023+00:00
-- url     : https://prove2.me/submissions/03e3bf88-956f-49f5-93ef-c67fe9441168

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ L : SimpleGraph V, P L ∧ G ≤ L ∧
      ∀ H : SimpleGraph V, P H → L ≤ H → H ≤ L := by
  classical
  let s : Set (SimpleGraph V) := {H | P H ∧ G ≤ H}
  have hs : s.Nonempty := ⟨G, hG, le_rfl⟩
  obtain ⟨L, hL, hmax⟩ := (Set.toFinite s).exists_maximal hs
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro H hH hLH
  exact hmax ⟨hH, le_trans hL.2 hLH⟩ hLH