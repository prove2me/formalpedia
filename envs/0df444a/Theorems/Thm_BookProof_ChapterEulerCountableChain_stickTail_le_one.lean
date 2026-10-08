-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_stickTail_le_one
-- name    : BookProof.ChapterEulerCountableChain.stickTail_le_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:33.395016+00:00
-- url     : https://prove2.me/theorems/765f65ed-440d-4d87-b8c5-9a4fd1139d19
-- title:
--   `BookProof.ChapterEulerCountableChain.stickTail_le_one` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) : stickTail c N ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.stickTail_le_one` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) : stickTail c N ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.stickTail_le_one`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.stickTail_le_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.stickTail_le_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (N : ℕ) :
    stickTail c N ≤ 1 := by sorry
