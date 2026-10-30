-- Prove2me | solution 1 for finite_graph_property_has_maximal_extension__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:34.562437+00:00
-- url     : https://prove2.me/submissions/8111de85-5dcd-4e74-9187-766e0aa7a50b

import Mathlib

theorem solution
    (V : Type) [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hmono : ∀ {G F : SimpleGraph V}, G ≤ F → P F → P G)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by
  classical
  obtain ⟨K, hHK, hK⟩ := Finite.exists_le_maximal (p := P) hH
  refine ⟨K, hHK, hK.prop, ?_⟩
  intro L hKL hPL
  exact (hK.eq_of_le hPL hKL).symm