-- Prove2me | solution 1 for maximal_drawable_graph_has_edge_extension__p2m_70fb6007_5dc1_4484_a53d_f6e6d3401839_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:01.01052+00:00
-- url     : https://prove2.me/submissions/a362d687-280c-42f4-9c3e-7ef62da77ab8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_maximal_drawable_graph_has_edge_extension_triangulation__p2m_869ffda5_b864_4783_a885_44fd746ff24a_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card < 3 * Fintype.card V - 6 →
      ∃ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧ ¬ L ≤ K := by
  letI : DecidableRel K.Adj := dK
  intro hsmall
  obtain ⟨L, hL, hKL, hstrict, _hcard⟩ :=
    maximal_drawable_graph_has_edge_extension_triangulation__p2m_869ffda5_b864_4783_a885_44fd746ff24a_a1
      K dK hK hn hsmall
  exact ⟨L, hL, hKL, hstrict⟩