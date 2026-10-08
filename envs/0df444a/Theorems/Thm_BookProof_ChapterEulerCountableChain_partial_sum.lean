-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_partial_sum
-- name    : BookProof.ChapterEulerCountableChain.partial_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:30.090638+00:00
-- url     : https://prove2.me/theorems/4ccc010e-cdb6-4dfa-aa00-2c9f0fd58005
-- title:
--   `BookProof.ChapterEulerCountableChain.partial_sum` (c : ℕ → ℝ) (N : ℕ) : ∑ n ∈ Finset.range N, stickProb c n = 1 - stickTail c N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.partial_sum` (c : ℕ → ℝ) (N : ℕ) : ∑ n ∈ Finset.range N, stickProb c n = 1 - stickTail c N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.partial_sum`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.partial_sum
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.partial_sum (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, stickProb c n = 1 - stickTail c N := by sorry
