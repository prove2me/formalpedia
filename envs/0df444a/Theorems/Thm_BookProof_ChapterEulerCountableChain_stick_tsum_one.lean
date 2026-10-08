-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_stick_tsum_one
-- name    : BookProof.ChapterEulerCountableChain.stick_tsum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:26.611429+00:00
-- url     : https://prove2.me/theorems/0c738c4e-62e2-4882-9e59-3ecce110bcc4
-- title:
--   `BookProof.ChapterEulerCountableChain.stick_tsum_one` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (htail : Tendsto (stickTail c) atTop (𝓝 0)) : ∑' n, stickProb c n = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.stick_tsum_one` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (htail : Tendsto (stickTail c) atTop (𝓝 0)) : ∑' n, stickProb c n = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.stick_tsum_one`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.stick_tsum_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.stick_tsum_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1)
    (htail : Tendsto (stickTail c) atTop (𝓝 0)) :
    ∑' n, stickProb c n = 1 := by sorry
