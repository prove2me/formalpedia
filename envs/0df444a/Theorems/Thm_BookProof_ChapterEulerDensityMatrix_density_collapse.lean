-- Prove2me | Theorems.Thm_BookProof_ChapterEulerDensityMatrix_density_collapse
-- name    : BookProof.ChapterEulerDensityMatrix.density_collapse
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:28:38.137803+00:00
-- url     : https://prove2.me/theorems/2a8c37af-f0d8-4b1f-8585-6bcdeab110c7
-- title:
--   `BookProof.ChapterEulerDensityMatrix.density_collapse` (t : ℝ) : densityMatrix t - (Real.sin (2 * t)) • (Zdiag * Jdens) = !![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerDensityMatrix`.
--
--   `BookProof.ChapterEulerDensityMatrix.density_collapse` (t : ℝ) : densityMatrix t - (Real.sin (2 * t)) • (Zdiag * Jdens) = !![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerDensityMatrix.density_collapse`.

-- Generated from ChapterEulerDensityMatrix.lean — theorem BookProof.ChapterEulerDensityMatrix.density_collapse
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix


open scoped Matrix

theorem BookProof.ChapterEulerDensityMatrix.density_collapse (t : ℝ) :
    densityMatrix t - (Real.sin (2 * t)) • (Zdiag * Jdens)
      = !![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2] := by sorry
