-- Prove2me | solution 1 for planar_drawing_completion_edge_count__p2m_f1fd84d6_ec35_411e_9342_50b2daa0def2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:34:29.110404+00:00
-- url     : https://prove2.me/submissions/cc9779ab-1671-4235-b14d-f7c142ad5c31

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2 L hV hL
  refine ⟨M, hLM, hM, ?_⟩
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  omega
