-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_stickTail_nonneg
-- name    : BookProof.ChapterEulerCountableChain.stickTail_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:04.14798+00:00
-- url     : https://prove2.me/theorems/d19014b7-37de-40ad-b023-e2b7a405e592
-- title:
--   `BookProof.ChapterEulerCountableChain.stickTail_nonneg` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) : 0 ≤ stickTail c N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.stickTail_nonneg` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) : 0 ≤ stickTail c N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.stickTail_nonneg`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.stickTail_nonneg
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.stickTail_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) :
    0 ≤ stickTail c N := by sorry
