-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_Jgen_mul
-- name    : BookProof.ChapterEulerGenericDensity.Jgen_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:29:57.002979+00:00
-- url     : https://prove2.me/theorems/9da12a39-60ed-4d42-839f-2c9a9f0e03d9
-- title:
--   `BookProof.ChapterEulerGenericDensity.Jgen_mul` (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : (Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.Jgen_mul` (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : (Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l w = Matrix.vecMulVec l w + Matrix.vecMulVec w l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.Jgen_mul`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.Jgen_mul
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.Jgen_mul (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    (Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l w
      = Matrix.vecMulVec l w + Matrix.vecMulVec w l := by sorry
