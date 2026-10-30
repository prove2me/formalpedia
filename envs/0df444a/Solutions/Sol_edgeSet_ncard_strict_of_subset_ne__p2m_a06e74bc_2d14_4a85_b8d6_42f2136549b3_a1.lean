-- Prove2me | solution 1 for edgeSet_ncard_strict_of_subset_ne__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:05.525087+00:00
-- url     : https://prove2.me/submissions/3d87c5c2-368c-45c2-ac04-2500e48f46f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (h : Set.Subset G.edgeSet H.edgeSet)
    (hne : G ≠ H) :
    G.edgeSet.ncard < H.edgeSet.ncard := by
  classical
  have hss : G.edgeSet ⊂ H.edgeSet := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨h, ?_⟩
    intro heq
    exact hne (SimpleGraph.edgeSet_inj.mp heq)
  have hfin : H.edgeSet.Finite := Set.toFinite H.edgeSet
  exact Set.ncard_lt_ncard hss hfin