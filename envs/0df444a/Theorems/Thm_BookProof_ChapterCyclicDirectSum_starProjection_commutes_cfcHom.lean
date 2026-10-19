-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDirectSum_starProjection_commutes_cfcHom
-- name    : BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:08:59.22928+00:00
-- url     : https://prove2.me/theorems/9c8de821-abbe-4b37-963e-3669a8965ccd
-- title:
--   `BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom` {M : Submodule ℂ H} [M.HasOrthogonalProjection] (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) (v : H) : M.starP
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDirectSum`.
--
--   `BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom` {M : Submodule ℂ H} [M.HasOrthogonalProjection] (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) (v : H) : M.starProjection (cfcHom hT g v) = cfcHom hT g (M.starProjection v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom`.

-- Generated from ChapterCyclicDirectSum.lean — theorem BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom
import Definitions.Def_ChapterCyclicDecomposition
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterCyclicDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) (v : H) :
    M.starProjection (cfcHom hT g v) = cfcHom hT g (M.starProjection v) := by sorry
