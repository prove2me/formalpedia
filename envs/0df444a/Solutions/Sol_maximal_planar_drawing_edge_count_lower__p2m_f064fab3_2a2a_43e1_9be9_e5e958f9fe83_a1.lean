-- Prove2me | solution 1 for maximal_planar_drawing_edge_count_lower__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:04:56.450044+00:00
-- url     : https://prove2.me/submissions/3efa69e6-4cee-47e9-a635-a5b9a7ef7893

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeFinset.card + 6 := by
  have h := WilliamsonShmoys.maximal_planar_edge_count_ge K hK hmax hcard
  have h_edges : K.edgeSet.ncard = K.edgeFinset.card := by
    simpa [SimpleGraph.edgeFinset] using
      (Set.ncard_eq_toFinset_card K.edgeSet (Set.toFinite K.edgeSet))
  simpa only [h_edges] using h
