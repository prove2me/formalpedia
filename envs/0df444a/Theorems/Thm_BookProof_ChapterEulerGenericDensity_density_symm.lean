-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_density_symm
-- name    : BookProof.ChapterEulerGenericDensity.density_symm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:30:42.227981+00:00
-- url     : https://prove2.me/theorems/fb030d17-f53a-4de7-ab3a-d5ed2e8849dd
-- title:
--   `BookProof.ChapterEulerGenericDensity.density_symm` (θ : ℝ) (l w : Fin d → ℝ) : (Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w))ᵀ = Matrix.vecMulVec (eulerVec θ l w) (eulerVec
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.density_symm` (θ : ℝ) (l w : Fin d → ℝ) : (Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w))ᵀ = Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.density_symm`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.density_symm
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.density_symm (θ : ℝ) (l w : Fin d → ℝ) :
    (Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w))ᵀ
      = Matrix.vecMulVec (eulerVec θ l w) (eulerVec θ l w) := by sorry
