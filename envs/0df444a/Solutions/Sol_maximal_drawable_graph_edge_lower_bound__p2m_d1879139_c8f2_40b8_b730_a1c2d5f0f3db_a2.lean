-- Prove2me | solution 1 for maximal_drawable_graph_edge_lower_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:39:46.732422+00:00
-- url     : https://prove2.me/submissions/188dc87b-b6f0-4b48-a5e3-a2841f755e5c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J → M ≤ J → J ≤ M)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     3 * Fintype.card V - 6 ≤ M.edgeFinset.card) := by
  apply WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3 M hn hM
  intro N hMN hN u v huv
  have hle : M ≤ N := by
    intro a b hab
    exact hMN a b hab
  exact hmax N hN hle huv
