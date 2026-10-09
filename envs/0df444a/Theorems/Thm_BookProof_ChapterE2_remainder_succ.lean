-- Prove2me | Theorems.Thm_BookProof_ChapterE2_remainder_succ
-- name    : BookProof.ChapterE2.remainder_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:10:30.976103+00:00
-- url     : https://prove2.me/theorems/40757239-f741-4e70-9e9a-a2e0b480ebdd
-- title:
--   `BookProof.ChapterE2.remainder_succ` (θ : ℕ → ℝ) (N : ℕ) : remainder θ (N + 1) = remainder θ N * Real.sin (θ N) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE2`.
--
--   `BookProof.ChapterE2.remainder_succ` (θ : ℕ → ℝ) (N : ℕ) : remainder θ (N + 1) = remainder θ N * Real.sin (θ N) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE2.remainder_succ`.

-- Generated from ChapterE2.lean — theorem BookProof.ChapterE2.remainder_succ
import Mathlib
import Definitions.Def_ChapterE2
open BookProof.ChapterE2


open scoped BigOperators
open Finset

theorem BookProof.ChapterE2.remainder_succ (θ : ℕ → ℝ) (N : ℕ) :
    remainder θ (N + 1) = remainder θ N * Real.sin (θ N) ^ 2 := by sorry
