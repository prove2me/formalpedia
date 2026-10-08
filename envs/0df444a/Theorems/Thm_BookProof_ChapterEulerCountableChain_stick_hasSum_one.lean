-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_stick_hasSum_one
-- name    : BookProof.ChapterEulerCountableChain.stick_hasSum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:39.937447+00:00
-- url     : https://prove2.me/theorems/7695fcce-557e-4cd0-ad2a-7089325eed6b
-- title:
--   `BookProof.ChapterEulerCountableChain.stick_hasSum_one` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (htail : Tendsto (stickTail c) atTop (𝓝 0)) : HasSum (stickProb c) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.stick_hasSum_one` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (htail : Tendsto (stickTail c) atTop (𝓝 0)) : HasSum (stickProb c) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.stick_hasSum_one`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.stick_hasSum_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.stick_hasSum_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1)
    (htail : Tendsto (stickTail c) atTop (𝓝 0)) :
    HasSum (stickProb c) 1 := by sorry
