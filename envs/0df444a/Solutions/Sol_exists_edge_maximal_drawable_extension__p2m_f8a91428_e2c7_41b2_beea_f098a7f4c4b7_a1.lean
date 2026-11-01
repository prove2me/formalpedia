-- Prove2me | solution 1 for exists_edge_maximal_drawable_extension__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:39.281414+00:00
-- url     : https://prove2.me/submissions/7ada7cfc-6d91-4b0b-940e-0b770e0d98f3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_finite_predicate_edge_maximal_extension__p2m_147a5295_4989_481d_a470_4dfaa73ce17a_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeFinset ⊆ K.edgeFinset ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeFinset ⊆ L.edgeFinset →
        L.edgeFinset ⊆ K.edgeFinset := by
  classical
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  obtain ⟨K, dK, hK, hNK, hmax⟩ :=
    exists_finite_predicate_edge_maximal_extension__p2m_147a5295_4989_481d_a470_4dfaa73ce17a_a1
      P N dN hN
  exact ⟨K, dK, hK, hNK, fun L dL hL hKL => hmax L dL hL hKL⟩