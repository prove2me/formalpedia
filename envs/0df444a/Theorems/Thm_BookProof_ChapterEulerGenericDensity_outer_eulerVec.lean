-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_outer_eulerVec
-- name    : BookProof.ChapterEulerGenericDensity.outer_eulerVec
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:29:31.447188+00:00
-- url     : https://prove2.me/theorems/6d1d30e7-5f9d-4bfc-9d9b-5fe7caece73c
-- title:
--   `BookProof.ChapterEulerGenericDensity.outer_eulerVec` (θ : ℝ) (l w : Fin d → ℝ) : Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) = (Real.cos θ ^ 2) • Matrix.vecMulVec l l + (Re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.outer_eulerVec` (θ : ℝ) (l w : Fin d → ℝ) : Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) = (Real.cos θ ^ 2) • Matrix.vecMulVec l l + (Real.sin θ ^ 2) • Matrix.vecMulVec w w + (Real.cos θ * Real.sin θ) • (Matrix.vecMulVec l w + Matrix.vecMulVec w l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.outer_eulerVec`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.outer_eulerVec
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.outer_eulerVec (θ : ℝ) (l w : Fin d → ℝ) :
    Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
      = (Real.cos θ ^ 2) • Matrix.vecMulVec l l
        + (Real.sin θ ^ 2) • Matrix.vecMulVec w w
        + (Real.cos θ * Real.sin θ) •
            (Matrix.vecMulVec l w + Matrix.vecMulVec w l) := by sorry
