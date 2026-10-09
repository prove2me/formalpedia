-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_density_idempotent
-- name    : BookProof.ChapterEulerGenericDensity.density_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:30:47.920076+00:00
-- url     : https://prove2.me/theorems/bae0fbe2-50e9-48d4-89e1-a75424082eb9
-- title:
--   `BookProof.ChapterEulerGenericDensity.density_idempotent` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.vecMulVec (eulerVec θ l w) (eu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.density_idempotent` (θ : ℝ) (l w : Fin d → ℝ) (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) : Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) * Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) = Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.density_idempotent`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.density_idempotent
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.density_idempotent (θ : ℝ) (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
        * Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
      = Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) := by sorry
