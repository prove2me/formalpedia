-- Prove2me | solution 1 for drawable_graph_has_maximal_drawable_extension__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:58:20.83503+00:00
-- url     : https://prove2.me/submissions/acaabce3-c23f-43c4-9895-79f57c96b827

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | WilliamsonShmoys.HasPlanarDrawingOn G ∧ H ≤ G}
  have hSfin : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  have hSne : S.Nonempty := ⟨H, hH, le_rfl⟩
  obtain ⟨K, hKS, hKmax⟩ := hSfin.exists_maximal hSne
  refine ⟨K, hKS.1, hKS.2, ?_⟩
  intro L hL hKL
  exact hKmax ⟨hL, hKS.2.trans hKL⟩ hKL