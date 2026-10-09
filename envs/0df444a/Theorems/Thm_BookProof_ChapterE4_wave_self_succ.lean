-- Prove2me | Theorems.Thm_BookProof_ChapterE4_wave_self_succ
-- name    : BookProof.ChapterE4.wave_self_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:13:54.389203+00:00
-- url     : https://prove2.me/theorems/19b9682f-d216-4dd5-9b12-ac3a2bf5ffd7
-- title:
--   `BookProof.ChapterE4.wave_self_succ` (θ : ℕ → ℝ) (s d : ℕ) : wave θ s (d + 1) s = Real.cos (θ s)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE4`.
--
--   `BookProof.ChapterE4.wave_self_succ` (θ : ℕ → ℝ) (s d : ℕ) : wave θ s (d + 1) s = Real.cos (θ s)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE4.wave_self_succ`.

-- Generated from ChapterE4.lean — theorem BookProof.ChapterE4.wave_self_succ
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4


open scoped BigOperators

theorem BookProof.ChapterE4.wave_self_succ (θ : ℕ → ℝ) (s d : ℕ) :
    wave θ s (d + 1) s = Real.cos (θ s) := by sorry
