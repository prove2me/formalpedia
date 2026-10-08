-- Prove2me | Theorems.Thm_BookProof_ChapterE4_diag_collapse
-- name    : BookProof.ChapterE4.diag_collapse
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:14:35.363864+00:00
-- url     : https://prove2.me/theorems/6fc22ed2-d628-4b87-99aa-141ddec010f6
-- title:
--   `BookProof.ChapterE4.diag_collapse` (θ : ℕ → ℝ) (s d i : ℕ) : (wave θ s (d + 1) i) ^ 2 = Real.cos (θ s) ^ 2 * (basisVec s i) ^ 2 + Real.sin (θ s) ^ 2 * (wave θ (s + 1) d i) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE4`.
--
--   `BookProof.ChapterE4.diag_collapse` (θ : ℕ → ℝ) (s d i : ℕ) : (wave θ s (d + 1) i) ^ 2 = Real.cos (θ s) ^ 2 * (basisVec s i) ^ 2 + Real.sin (θ s) ^ 2 * (wave θ (s + 1) d i) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE4.diag_collapse`.

-- Generated from ChapterE4.lean — theorem BookProof.ChapterE4.diag_collapse
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4


open scoped BigOperators

theorem BookProof.ChapterE4.diag_collapse (θ : ℕ → ℝ) (s d i : ℕ) :
    (wave θ s (d + 1) i) ^ 2
      = Real.cos (θ s) ^ 2 * (basisVec s i) ^ 2
        + Real.sin (θ s) ^ 2 * (wave θ (s + 1) d i) ^ 2 := by sorry
