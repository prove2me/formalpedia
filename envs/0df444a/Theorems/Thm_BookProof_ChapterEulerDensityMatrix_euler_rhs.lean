-- Prove2me | Theorems.Thm_BookProof_ChapterEulerDensityMatrix_euler_rhs
-- name    : BookProof.ChapterEulerDensityMatrix.euler_rhs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:28:46.547536+00:00
-- url     : https://prove2.me/theorems/28375b5b-582c-4072-9d10-d58a1f6af85a
-- title:
--   `BookProof.ChapterEulerDensityMatrix.euler_rhs` (t : ℝ) : (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (Real.sin (2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerDensityMatrix`.
--
--   `BookProof.ChapterEulerDensityMatrix.euler_rhs` (t : ℝ) : (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (Real.sin (2 * t)) • Jdens) = !![1 / 2 + Real.cos (2 * t) / 2, Real.sin (2 * t) / 2; Real.sin (2 * t) / 2, 1 / 2 - Real.cos (2 * t) / 2]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerDensityMatrix.euler_rhs`.

-- Generated from ChapterEulerDensityMatrix.lean — theorem BookProof.ChapterEulerDensityMatrix.euler_rhs
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix


open scoped Matrix

theorem BookProof.ChapterEulerDensityMatrix.euler_rhs (t : ℝ) :
    (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + Zdiag * ((Real.cos (2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
            + (Real.sin (2 * t)) • Jdens)
      = !![1 / 2 + Real.cos (2 * t) / 2, Real.sin (2 * t) / 2;
           Real.sin (2 * t) / 2, 1 / 2 - Real.cos (2 * t) / 2] := by sorry
