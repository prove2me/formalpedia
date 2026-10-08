-- Prove2me | Theorems.Thm_BookProof_ChapterEulerDensityMatrix_densityMatrix_eq
-- name    : BookProof.ChapterEulerDensityMatrix.densityMatrix_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:27:54.79412+00:00
-- url     : https://prove2.me/theorems/73da13f2-383a-430d-aafc-3b83b93707bc
-- title:
--   `BookProof.ChapterEulerDensityMatrix.densityMatrix_eq` (t : ℝ) : densityMatrix t = !![Real.cos t ^ 2, Real.cos t * Real.sin t; Real.cos t * Real.sin t, Real.sin t ^ 2]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerDensityMatrix`.
--
--   `BookProof.ChapterEulerDensityMatrix.densityMatrix_eq` (t : ℝ) : densityMatrix t = !![Real.cos t ^ 2, Real.cos t * Real.sin t; Real.cos t * Real.sin t, Real.sin t ^ 2]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerDensityMatrix.densityMatrix_eq`.

-- Generated from ChapterEulerDensityMatrix.lean — theorem BookProof.ChapterEulerDensityMatrix.densityMatrix_eq
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix


open scoped Matrix

theorem BookProof.ChapterEulerDensityMatrix.densityMatrix_eq (t : ℝ) :
    densityMatrix t =
      !![Real.cos t ^ 2, Real.cos t * Real.sin t;
         Real.cos t * Real.sin t, Real.sin t ^ 2] := by sorry
