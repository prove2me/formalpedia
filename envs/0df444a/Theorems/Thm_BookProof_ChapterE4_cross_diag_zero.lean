-- Prove2me | Theorems.Thm_BookProof_ChapterE4_cross_diag_zero
-- name    : BookProof.ChapterE4.cross_diag_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:14:19.694214+00:00
-- url     : https://prove2.me/theorems/a686a024-a8a1-4a80-8d41-2288fa2e0f25
-- title:
--   `BookProof.ChapterE4.cross_diag_zero` (θ : ℕ → ℝ) (s d i : ℕ) : basisVec s i * wave θ (s + 1) d i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE4`.
--
--   `BookProof.ChapterE4.cross_diag_zero` (θ : ℕ → ℝ) (s d i : ℕ) : basisVec s i * wave θ (s + 1) d i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE4.cross_diag_zero`.

-- Generated from ChapterE4.lean — theorem BookProof.ChapterE4.cross_diag_zero
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4


open scoped BigOperators

theorem BookProof.ChapterE4.cross_diag_zero (θ : ℕ → ℝ) (s d i : ℕ) :
    basisVec s i * wave θ (s + 1) d i = 0 := by sorry
