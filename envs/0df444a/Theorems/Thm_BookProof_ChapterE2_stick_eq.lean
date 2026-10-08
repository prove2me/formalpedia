-- Prove2me | Theorems.Thm_BookProof_ChapterE2_stick_eq
-- name    : BookProof.ChapterE2.stick_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:11:02.932404+00:00
-- url     : https://prove2.me/theorems/dcbb9ffc-57db-4864-a373-4ec9656a1cf3
-- title:
--   `BookProof.ChapterE2.stick_eq` (θ : ℕ → ℝ) (n : ℕ) : stick θ n = remainder θ n * Real.cos (θ n) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE2`.
--
--   `BookProof.ChapterE2.stick_eq` (θ : ℕ → ℝ) (n : ℕ) : stick θ n = remainder θ n * Real.cos (θ n) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE2.stick_eq`.

-- Generated from ChapterE2.lean — theorem BookProof.ChapterE2.stick_eq
import Mathlib
import Definitions.Def_ChapterE2
open BookProof.ChapterE2


open scoped BigOperators
open Finset

theorem BookProof.ChapterE2.stick_eq (θ : ℕ → ℝ) (n : ℕ) :
    stick θ n = remainder θ n * Real.cos (θ n) ^ 2 := by sorry
