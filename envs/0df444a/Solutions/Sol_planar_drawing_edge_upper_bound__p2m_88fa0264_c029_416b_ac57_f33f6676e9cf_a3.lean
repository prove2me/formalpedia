-- Prove2me | solution 1 for planar_drawing_edge_upper_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:36:58.46491+00:00
-- url     : https://prove2.me/submissions/a1226e11-2a36-4563-8cd6-ca99f65d94ce

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  exact WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1 L hV hL
