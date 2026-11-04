-- Prove2me | solution 1 for maximal_planar_drawing_edge_lower_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:48:19.909931+00:00
-- url     : https://prove2.me/submissions/988a9a75-b39e-4ba4-a052-0a9084f1a9b8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_completion_edge_count__p2m_f1fd84d6_ec35_411e_9342_50b2daa0def2_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by
  classical
  obtain ⟨M, hLM, hM, hcard⟩ :=
    planar_drawing_completion_edge_count__p2m_f1fd84d6_ec35_411e_9342_50b2daa0def2_a1
      L hV hL
  have hEq : M = L := hmax M hLM hM
  have hcardL : L.edgeFinset.card = M.edgeFinset.card := by
    rw [← hEq]
  rw [← hcardL] at hcard
  omega