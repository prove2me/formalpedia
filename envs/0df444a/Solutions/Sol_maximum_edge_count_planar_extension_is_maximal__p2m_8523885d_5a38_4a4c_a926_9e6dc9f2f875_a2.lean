-- Prove2me | solution 1 for maximum_edge_count_planar_extension_is_maximal__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:10:44.981636+00:00
-- url     : https://prove2.me/submissions/84adcda5-9b82-439e-88c0-356c5e1ddfe8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hHDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  intro K hHK hK
  have hle := hmax K (hGH.trans hHK) hK
  exact (SimpleGraph.edgeSet_injective (Set.eq_of_subset_of_ncard_le
    (SimpleGraph.edgeSet_subset_edgeSet.2 hHK) hle (Set.toFinite _))).symm
