-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_stickProb_euler
-- name    : BookProof.ChapterEulerCountableChain.stickProb_euler
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:45.147771+00:00
-- url     : https://prove2.me/theorems/2a484565-8343-496f-bc9d-17737ea3ee51
-- title:
--   `BookProof.ChapterEulerCountableChain.stickProb_euler` (θ : ℕ → ℝ) (n : ℕ) : stickProb (condCos θ) n = (∏ k ∈ Finset.range n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.stickProb_euler` (θ : ℕ → ℝ) (n : ℕ) : stickProb (condCos θ) n = (∏ k ∈ Finset.range n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.stickProb_euler`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.stickProb_euler
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.stickProb_euler (θ : ℕ → ℝ) (n : ℕ) :
    stickProb (condCos θ) n
      = (∏ k ∈ Finset.range n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2 := by sorry
