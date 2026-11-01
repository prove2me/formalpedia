-- Prove2me | solution 1 for finite_graph_predicate_maximal_extension__p2m_5e22ecc2_fcd1_4580_86fc_2603fce53c32_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:44.739381+00:00
-- url     : https://prove2.me/submissions/2d653dc9-3a03-4569-8661-411d62e1a442

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ G : SimpleGraph V, K ≤ G ∧ P G ∧
      ∀ H : SimpleGraph V, G ≤ H → P H → H ≤ G := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ P G}
  have hS_finite : S.Finite :=
    Set.finite_univ.subset (by intro G hG; trivial)
  have hS_nonempty : S.Nonempty := by
    exact ⟨K, ⟨le_rfl, hK⟩⟩
  obtain ⟨G, hG, hG_max⟩ := hS_finite.exists_maximal hS_nonempty
  refine ⟨G, hG.1, hG.2, ?_⟩
  intro H hGH hH
  exact hG_max ⟨hG.1.trans hGH, hH⟩ hGH