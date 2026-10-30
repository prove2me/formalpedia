-- Prove2me | solution 1 for maximal_planar_edge_bound__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:23.472621+00:00
-- url     : https://prove2.me/submissions/793dba78-1a97-4ef0-8eff-b883042ba998
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planarDrawing_completion_edge_count__p2m_9248cd60_7dc5_457e_b64c_c24bd6929c95_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : ∀ M : SimpleGraph V, LE.le L M →
      HasPlanarDrawingOn M → M = L) :
    LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6) := by
  obtain ⟨M, hLM, hM, hcard⟩ :=
    planarDrawing_completion_edge_count__p2m_9248cd60_7dc5_457e_b64c_c24bd6929c95_a2
      (V := V) L hL hV
  have hML : M = L := hmax M hLM hM
  simpa [hML] using hcard.le
