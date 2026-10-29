-- Prove2me | solution 2 for maximum_edge_count_planar_extension_is_maximal__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:59.661831+00:00
-- url     : https://prove2.me/submissions/fdbe8f7b-f9d9-465c-b18d-7716325ef305

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
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
  have h1 : K.edgeSet.ncard ≤ H.edgeSet.ncard := hmax K (le_trans hGH hHK) hK
  have h2 : H.edgeSet ⊆ K.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hHK
  have h3 : H.edgeSet = K.edgeSet := Set.eq_of_subset_of_ncard_le h2 h1 (Set.toFinite _)
  exact (SimpleGraph.edgeSet_inj.mp h3).symm
