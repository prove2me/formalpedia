-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_stickProb_nonneg
-- name    : BookProof.ChapterEulerCountableChain.stickProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:25:56.678986+00:00
-- url     : https://prove2.me/theorems/3c4ee836-0318-47ad-82d7-54f42b0ee3fe
-- title:
--   `BookProof.ChapterEulerCountableChain.stickProb_nonneg` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (n : ℕ) : 0 ≤ stickProb c n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.stickProb_nonneg` (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (n : ℕ) : 0 ≤ stickProb c n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.stickProb_nonneg`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.stickProb_nonneg
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.stickProb_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1) (n : ℕ) :
    0 ≤ stickProb c n := by sorry
