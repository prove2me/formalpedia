-- Prove2me | Theorems.Thm_BookProof_ChapterEulerDensityMatrix_density_euler
-- name    : BookProof.ChapterEulerDensityMatrix.density_euler
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:28:25.17372+00:00
-- url     : https://prove2.me/theorems/fa24e685-fed1-4273-a7f9-8a3a6bfab1c0
-- title:
--   `BookProof.ChapterEulerDensityMatrix.density_euler` (t : ℝ) : densityMatrix t = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerDensityMatrix`.
--
--   `BookProof.ChapterEulerDensityMatrix.density_euler` (t : ℝ) : densityMatrix t = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (Real.sin (2 * t)) • Jdens)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerDensityMatrix.density_euler`.

-- Generated from ChapterEulerDensityMatrix.lean — theorem BookProof.ChapterEulerDensityMatrix.density_euler
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix


open scoped Matrix

theorem BookProof.ChapterEulerDensityMatrix.density_euler (t : ℝ) :
    densityMatrix t =
      (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
            + (Real.sin (2 * t)) • Jdens) := by sorry
