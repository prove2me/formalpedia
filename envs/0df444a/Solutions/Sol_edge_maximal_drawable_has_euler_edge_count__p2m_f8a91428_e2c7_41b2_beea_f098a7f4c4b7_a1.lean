-- Prove2me | solution 1 for edge_maximal_drawable_has_euler_edge_count__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:46.458213+00:00
-- url     : https://prove2.me/submissions/7df8cf67-e907-4575-b554-548cde5a1625
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_with_euler_edge_count__p2m_ef27f67c_bfde_4fe0_af12_0939b2f8ce56_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset →
      L.edgeFinset ⊆ K.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨L, dL, hL, hKL, hcount⟩ :=
    WilliamsonShmoys_planar_drawing_completion_with_euler_edge_count__p2m_ef27f67c_bfde_4fe0_af12_0939b2f8ce56_a2
      K dK hK hcard
  have hLK : L.edgeFinset ⊆ K.edgeFinset := hmax L dL hL hKL
  have heq : K.edgeFinset = L.edgeFinset := Finset.Subset.antisymm hKL hLK
  simpa only [heq] using hcount