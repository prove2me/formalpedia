-- Prove2me | solution 1 for planar_drawing_maximal_extension__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:35.377277+00:00
-- url     : https://prove2.me/submissions/032425af-7227-4f5e-ba40-18677e062f36

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let feasible : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hfeasible : ∃ G, feasible G := ⟨K, le_rfl, hK⟩
  obtain ⟨L, instL, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists feasible).2 hfeasible
  letI : DecidableRel L.Adj := instL
  refine ⟨L, hmax.prop.1, hmax.prop.2, ?_⟩
  intro M hLM hM
  have hMfeasible : feasible M := ⟨hmax.prop.1.trans hLM, hM⟩
  exact ((hmax.le_iff_eq hMfeasible).mp hLM).symm