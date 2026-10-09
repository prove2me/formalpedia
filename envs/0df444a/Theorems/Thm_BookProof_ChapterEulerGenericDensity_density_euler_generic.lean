-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_density_euler_generic
-- name    : BookProof.ChapterEulerGenericDensity.density_euler_generic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:29:54.517859+00:00
-- url     : https://prove2.me/theorems/fe7fac49-e3f6-4a9c-8568-e220357b9c61
-- title:
--   `BookProof.ChapterEulerGenericDensity.density_euler_generic` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.vecMulVec (eulerVec θ l w)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.density_euler_generic` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) = (1 / 2 : ℝ) • (Matrix.vecMulVec l l + Matrix.vecMulVec w w) + (Real.cos (2 * θ) / 2) • (Matrix.vecMulVec l l - Matrix.vecMulVec w w) + (Real.sin (2 * θ) / 2) • ((Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l w)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.density_euler_generic`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.density_euler_generic
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.density_euler_generic (θ : ℝ) (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
      = (1 / 2 : ℝ) • (Matrix.vecMulVec l l + Matrix.vecMulVec w w)
        + (Real.cos (2 * θ) / 2) • (Matrix.vecMulVec l l - Matrix.vecMulVec w w)
        + (Real.sin (2 * θ) / 2) •
            ((Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l w) := by sorry
