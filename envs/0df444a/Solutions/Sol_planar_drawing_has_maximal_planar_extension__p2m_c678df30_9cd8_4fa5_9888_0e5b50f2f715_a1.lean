-- Prove2me | solution 1 for planar_drawing_has_maximal_planar_extension__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:32:11.599812+00:00
-- url     : https://prove2.me/submissions/dcced567-66f2-4d6d-b1ac-204d451ed93f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

/-- Restricting a crossing-free drawing to fewer edges preserves the drawing. -/
theorem planarDrawingOn_mono__p2m_30717a8b_f004_4e88_a3d7_0eab2997311e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {H G : SimpleGraph V} (hHG : H ≤ G)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hedges, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedges u v huv (hHG hadj)
  · intro u v x y huv hxy hadj hxyadj hneq t ht s hs heq
    exact hcross u v x y huv hxy (hHG hadj) (hHG hxyadj) hneq t ht s hs heq

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (K' : SimpleGraph V) (dK' : DecidableRel K'.Adj),
      K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧
        ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
          K' ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K' := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hS : S.Finite := Set.toFinite S
  obtain ⟨K', hK'max⟩ := hS.exists_maximal ⟨K, le_rfl, hK⟩
  have hK'mem : K' ∈ S := hK'max.1
  rcases hK'mem with ⟨hKK', hK'planar⟩
  refine ⟨K', inferInstance, hKK', hK'planar, ?_⟩
  intro H dH hK'H hHplanar
  have hHmem : H ∈ S := ⟨le_trans hKK' hK'H, hHplanar⟩
  exact hK'max.2 (y := H) hHmem hK'H