-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_Jgen_sq
-- name    : BookProof.ChapterEulerGenericDensity.Jgen_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:29:38.22217+00:00
-- url     : https://prove2.me/theorems/cf7ade28-ca25-4ffc-b58d-d9f256a9b9ac
-- title:
--   `BookProof.ChapterEulerGenericDensity.Jgen_sq` (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Jgen l w * Jgen l w = -(Matrix.vecMulVec l l + Matrix.ve
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.Jgen_sq` (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Jgen l w * Jgen l w = -(Matrix.vecMulVec l l + Matrix.vecMulVec w w)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.Jgen_sq`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.Jgen_sq
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.Jgen_sq (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    Jgen l w * Jgen l w = -(Matrix.vecMulVec l l + Matrix.vecMulVec w w) := by sorry
