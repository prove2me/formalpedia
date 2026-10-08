-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_vecMulVec_mul_vecMulVec
-- name    : BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:29:20.881894+00:00
-- url     : https://prove2.me/theorems/b10cf79a-3c45-4353-bb8c-e1eaf9895d2a
-- title:
--   `BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec` (u v x y : Fin d → ℝ) : Matrix.vecMulVec u v * Matrix.vecMulVec x y = (v ⬝ᵥ x) • Matrix.vecMulVec u y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec` (u v x y : Fin d → ℝ) : Matrix.vecMulVec u v * Matrix.vecMulVec x y = (v ⬝ᵥ x) • Matrix.vecMulVec u y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec (u v x y : Fin d → ℝ) :
    Matrix.vecMulVec u v * Matrix.vecMulVec x y = (v ⬝ᵥ x) • Matrix.vecMulVec u y := by sorry
