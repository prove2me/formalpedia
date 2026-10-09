-- Prove2me | Theorems.Thm_BookProof_ChapterEulerGenericDensity_conditional_probability_at
-- name    : BookProof.ChapterEulerGenericDensity.conditional_probability_at
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:31:39.240992+00:00
-- url     : https://prove2.me/theorems/f33d9c7c-ebc5-4b1c-93ca-dc6246000534
-- title:
--   `BookProof.ChapterEulerGenericDensity.conditional_probability_at` (θ : ℝ) (l w : Fin d → ℝ) (k : Fin d) (hlk : l k = 1) (hwk : w k = 0) : ((Real.cos θ ^ 2) • Matrix.vecMulVec l l +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerGenericDensity`.
--
--   `BookProof.ChapterEulerGenericDensity.conditional_probability_at` (θ : ℝ) (l w : Fin d → ℝ) (k : Fin d) (hlk : l k = 1) (hwk : w k = 0) : ((Real.cos θ ^ 2) • Matrix.vecMulVec l l + (Real.sin θ ^ 2) • Matrix.vecMulVec w w) k k = Real.cos θ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerGenericDensity.conditional_probability_at`.

-- Generated from ChapterEulerGenericDensity.lean — theorem BookProof.ChapterEulerGenericDensity.conditional_probability_at
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity


open scoped Matrix
open Matrix


variable {d : ℕ}

theorem BookProof.ChapterEulerGenericDensity.conditional_probability_at (θ : ℝ) (l w : Fin d → ℝ)
    (k : Fin d) (hlk : l k = 1) (hwk : w k = 0) :
    ((Real.cos θ ^ 2) • Matrix.vecMulVec l l
      + (Real.sin θ ^ 2) • Matrix.vecMulVec w w) k k = Real.cos θ ^ 2 := by sorry
