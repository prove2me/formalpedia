-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_density_trace
-- name    : BookProof.ChapterEulerGenericDensity.density_trace
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:30:23.40926+00:00
-- url     : https://prove2.me/theorems/9900346f-3364-4976-920b-30687f85bf08
-- title:
--   `BookProof.ChapterEulerGenericDensity.density_trace` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.trace (Matrix.vecMulVec (eulerVec θ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.density_trace` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.trace (Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.density_trace`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.density_trace
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.density_trace (θ : ℝ) (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    Matrix.trace (Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)) = 1 := by sorry
