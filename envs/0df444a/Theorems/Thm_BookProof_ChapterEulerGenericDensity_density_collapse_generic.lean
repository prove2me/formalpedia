-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_density_collapse_generic
-- name    : BookProof.ChapterEulerGenericDensity.density_collapse_generic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:34:02.336023+00:00
-- url     : https://prove2.me/theorems/c9bcf5cb-1007-4cad-ac75-479537b678b3
-- title:
--   `BookProof.ChapterEulerGenericDensity.density_collapse_generic` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.vecMulVec (eulerVec θ l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.density_collapse_generic` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) - (Real.sin (2 * θ) / 2) • ((Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l w) = (Real.cos θ ^ 2) • Matrix.vecMulVec l l + (Real.sin θ ^ 2) • Matrix.vecMulVec w w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.density_collapse_generic`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.density_collapse_generic
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.density_collapse_generic (θ : ℝ) (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
        - (Real.sin (2 * θ) / 2) •
            ((Matrix.vecMulVec l l - Matrix.vecMulVec w w) * Jgen l w)
      = (Real.cos θ ^ 2) • Matrix.vecMulVec l l
        + (Real.sin θ ^ 2) • Matrix.vecMulVec w w := by sorry
