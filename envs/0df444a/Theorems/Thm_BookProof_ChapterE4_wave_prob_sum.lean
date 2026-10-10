-- Prove2me | Theorems.Thm_BookProof_ChapterE4_wave_prob_sum
-- name    : BookProof.ChapterE4.wave_prob_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:15:35.474345+00:00
-- url     : https://prove2.me/theorems/857eea56-5810-424e-8f42-0157b994a822
-- title:
--   `BookProof.ChapterE4.wave_prob_sum` (θ : ℕ → ℝ) (s d : ℕ) : ∑ i ∈ Finset.Icc s (s + d), (wave θ s d i) ^ 2 = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE4`.
--
--   `BookProof.ChapterE4.wave_prob_sum` (θ : ℕ → ℝ) (s d : ℕ) : ∑ i ∈ Finset.Icc s (s + d), (wave θ s d i) ^ 2 = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE4.wave_prob_sum`.

-- Generated from ChapterE4.lean — theorem BookProof.ChapterE4.wave_prob_sum
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4


open scoped BigOperators

theorem BookProof.ChapterE4.wave_prob_sum (θ : ℕ → ℝ) (s d : ℕ) :
    ∑ i ∈ Finset.Icc s (s + d), (wave θ s d i) ^ 2 = 1 := by sorry
