-- Prove2me | solution 1 for finite_planar_extension_max_edge_count__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:11:01.500992+00:00
-- url     : https://prove2.me/submissions/b57216cf-5726-4799-8733-95b43544cac6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, G ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨H, ⟨hGH, hH⟩, hmax⟩ := Set.exists_max_image {K : SimpleGraph V | G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
    (fun K => K.edgeSet.ncard) (Set.toFinite _) ⟨G, le_rfl, hDraw⟩
  exact ⟨H, hGH, SimpleGraph.edgeSet_subset_edgeSet.2 hGH, hH, fun K hGK hK => hmax K ⟨hGK, hK⟩⟩
