-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDirectSum_commute_starProjection_cfcHom
-- name    : BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:09:08.90005+00:00
-- url     : https://prove2.me/theorems/1e7362e5-2d0b-43b3-9ab0-d863b8fe0959
-- title:
--   `BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom` {M : Submodule ℂ H} [M.HasOrthogonalProjection] (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) : Commute M.starPr
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDirectSum`.
--
--   `BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom` {M : Submodule ℂ H} [M.HasOrthogonalProjection] (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) : Commute M.starProjection (cfcHom hT g)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom`.

-- Generated from ChapterCyclicDirectSum.lean — theorem BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom
import Definitions.Def_ChapterCyclicDecomposition
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterCyclicDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) :
    Commute M.starProjection (cfcHom hT g) := by sorry
