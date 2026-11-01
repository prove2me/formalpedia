-- Prove2me | solution 1 for planar_drawing_edge_count_upper__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:39.585994+00:00
-- url     : https://prove2.me/submissions/3d608478-eeda-4eda-90c4-ec3908ebcc6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨N, hKN, hN, hcard_le, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
      K hK
  have hNexact :=
    WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
      N hcard hN hmax
  have hle : K.edgeFinset.card ≤ N.edgeSet.ncard := hcard_le
  omega