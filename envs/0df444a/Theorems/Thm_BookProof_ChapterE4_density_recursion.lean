-- Prove2me | Theorems.Thm_BookProof_ChapterE4_density_recursion
-- name    : BookProof.ChapterE4.density_recursion
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:14:01.710133+00:00
-- url     : https://prove2.me/theorems/0c5a02e0-54c4-4152-be3b-523867d5c467
-- title:
--   `BookProof.ChapterE4.density_recursion` (θ : ℕ → ℝ) (s d i j : ℕ) : wave θ s (d + 1) i * wave θ s (d + 1) j = Real.cos (θ s) ^ 2 * (basisVec s i * basisVec s j) + Real.sin (θ s) ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE4`.
--
--   `BookProof.ChapterE4.density_recursion` (θ : ℕ → ℝ) (s d i j : ℕ) : wave θ s (d + 1) i * wave θ s (d + 1) j = Real.cos (θ s) ^ 2 * (basisVec s i * basisVec s j) + Real.sin (θ s) ^ 2 * (wave θ (s + 1) d i * wave θ (s + 1) d j) + Real.cos (θ s) * Real.sin (θ s) * (basisVec s i * wave θ (s + 1) d j + wave θ (s + 1) d i * basisVec s j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE4.density_recursion`.

-- Generated from ChapterE4.lean — theorem BookProof.ChapterE4.density_recursion
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4


open scoped BigOperators

theorem BookProof.ChapterE4.density_recursion (θ : ℕ → ℝ) (s d i j : ℕ) :
    wave θ s (d + 1) i * wave θ s (d + 1) j
      = Real.cos (θ s) ^ 2 * (basisVec s i * basisVec s j)
        + Real.sin (θ s) ^ 2 * (wave θ (s + 1) d i * wave θ (s + 1) d j)
        + Real.cos (θ s) * Real.sin (θ s) *
            (basisVec s i * wave θ (s + 1) d j + wave θ (s + 1) d i * basisVec s j) := by sorry
