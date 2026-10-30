-- Prove2me | solution 1 for exists_edge_maximal_subgraph_above__p2m_8f0c4e79_82ed_4eab_8262_744ee1ed1865_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:05:36.537026+00:00
-- url     : https://prove2.me/submissions/4363ba05-b7bc-491e-99fc-ccf015892486

import Theorems.Thm_finite_type_has_maximal_element__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
import Theorems.Thm_finite_simplegraph__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hdown : ∀ G H : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet → P G → P H) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        P M →
        M.edgeSet ⊆ L.edgeSet := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ P G}
  have hS : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hLS, hmax⟩ :=
    finite_type_has_maximal_element__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1 S hS
  rcases hLS with ⟨hKL, hPL⟩
  refine ⟨L, ?_, hPL, ?_⟩
  · simpa using hKL
  · intro M hLM hPM
    have hKM : K ≤ M := le_trans hKL (by simpa using hLM)
    have hM : M ∈ S := ⟨hKM, hPM⟩
    have hML := hmax M hM (by simpa using hLM)
    simpa using hML