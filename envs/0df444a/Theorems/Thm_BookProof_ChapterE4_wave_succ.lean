-- Prove2me | Theorems.Thm_BookProof_ChapterE4_wave_succ
-- name    : BookProof.ChapterE4.wave_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:13:22.718741+00:00
-- url     : https://prove2.me/theorems/1776596f-eb5a-4526-8e4b-7998c82311bc
-- title:
--   `BookProof.ChapterE4.wave_succ` (θ : ℕ → ℝ) (s d : ℕ) (i : ℕ) : wave θ s (d + 1) i = Real.cos (θ s) * basisVec s i + Real.sin (θ s) * wave θ (s + 1) d i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE4`.
--
--   `BookProof.ChapterE4.wave_succ` (θ : ℕ → ℝ) (s d : ℕ) (i : ℕ) : wave θ s (d + 1) i = Real.cos (θ s) * basisVec s i + Real.sin (θ s) * wave θ (s + 1) d i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE4.wave_succ`.

-- Generated from ChapterE4.lean — theorem BookProof.ChapterE4.wave_succ
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4


open scoped BigOperators

theorem BookProof.ChapterE4.wave_succ (θ : ℕ → ℝ) (s d : ℕ) (i : ℕ) :
    wave θ s (d + 1) i =
      Real.cos (θ s) * basisVec s i + Real.sin (θ s) * wave θ (s + 1) d i := by sorry
