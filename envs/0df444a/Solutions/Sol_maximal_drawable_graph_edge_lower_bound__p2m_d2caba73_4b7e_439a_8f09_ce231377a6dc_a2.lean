-- Prove2me | solution 1 for maximal_drawable_graph_edge_lower_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:27:18.465963+00:00
-- url     : https://prove2.me/submissions/e81de70b-e8a9-43ff-9639-889eaf6aeb6a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_maximal_drawable_graph_has_edge_extension__p2m_70fb6007_5dc1_4484_a53d_f6e6d3401839_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    letI : DecidableRel K.Adj := dK
    3 * Fintype.card V - 6 <= K.edgeFinset.card := by
  letI : DecidableRel K.Adj := dK
  by_contra h
  have hsmall : K.edgeFinset.card < 3 * Fintype.card V - 6 := Nat.not_le.mp h
  obtain ⟨L, hL, hKL, hnotLK⟩ :=
    maximal_drawable_graph_has_edge_extension__p2m_70fb6007_5dc1_4484_a53d_f6e6d3401839_a1
      K dK hK hn hsmall
  exact hnotLK (hmax L hL hKL)