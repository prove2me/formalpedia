-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_proj_sum
-- name    : BookProof.ChapterWeakValue.weakValue_proj_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:15.51568+00:00
-- url     : https://prove2.me/theorems/15926075-0d2e-4973-956b-7f2c3ec59dd3
-- title:
--   `BookProof.ChapterWeakValue.weakValue_proj_sum` (i f : Fin n → ℂ) (h : ip f i ≠ 0) : ∑ a, weakValue i f (projMat a) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_proj_sum` (i f : Fin n → ℂ) (h : ip f i ≠ 0) : ∑ a, weakValue i f (projMat a) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_proj_sum`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_proj_sum
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_proj_sum (i f : Fin n → ℂ) (h : ip f i ≠ 0) :
    ∑ a, weakValue i f (projMat a) = 1 := by sorry
