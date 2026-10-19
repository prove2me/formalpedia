-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDirectSum_starProjection_cyclicSubspace_commutes
-- name    : BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:09:20.403431+00:00
-- url     : https://prove2.me/theorems/022819ef-41e9-49b7-8ba7-98e2d4890b41
-- title:
--   `BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes` (xi : H) (g : C(spectrum ℂ T, ℂ)) : Commute (cyclicSubspace T hT xi).starProjection (cfcHom hT g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDirectSum`.
--
--   `BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes` (xi : H) (g : C(spectrum ℂ T, ℂ)) : Commute (cyclicSubspace T hT xi).starProjection (cfcHom hT g)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes`.

-- Generated from ChapterCyclicDirectSum.lean — theorem BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes
import Definitions.Def_ChapterCyclicDecomposition
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterCyclicDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes (xi : H) (g : C(spectrum ℂ T, ℂ)) :
    Commute (cyclicSubspace T hT xi).starProjection (cfcHom hT g) := by sorry
