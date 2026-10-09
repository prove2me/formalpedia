-- Prove2me | Theorems.Thm_BookProof_ChapterEulerDensityMatrix_densityMatrix_idempotent
-- name    : BookProof.ChapterEulerDensityMatrix.densityMatrix_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:29:06.135105+00:00
-- url     : https://prove2.me/theorems/972d0132-0092-4907-9afe-094370d3fabf
-- title:
--   `BookProof.ChapterEulerDensityMatrix.densityMatrix_idempotent` (t : ℝ) : densityMatrix t * densityMatrix t = densityMatrix t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerDensityMatrix`.
--
--   `BookProof.ChapterEulerDensityMatrix.densityMatrix_idempotent` (t : ℝ) : densityMatrix t * densityMatrix t = densityMatrix t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerDensityMatrix.densityMatrix_idempotent`.

-- Generated from ChapterEulerDensityMatrix.lean — theorem BookProof.ChapterEulerDensityMatrix.densityMatrix_idempotent
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix


open scoped Matrix

theorem BookProof.ChapterEulerDensityMatrix.densityMatrix_idempotent (t : ℝ) :
    densityMatrix t * densityMatrix t = densityMatrix t := by sorry
