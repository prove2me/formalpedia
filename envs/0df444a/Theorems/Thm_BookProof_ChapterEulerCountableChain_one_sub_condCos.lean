-- Prove2me | Theorems.Thm_BookProof_ChapterEulerCountableChain_one_sub_condCos
-- name    : BookProof.ChapterEulerCountableChain.one_sub_condCos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:26:34.719342+00:00
-- url     : https://prove2.me/theorems/34c0e732-e0df-4ecc-af7a-da9b1159bad5
-- title:
--   `BookProof.ChapterEulerCountableChain.one_sub_condCos` (θ : ℕ → ℝ) (n : ℕ) : 1 - condCos θ n = Real.sin (θ n) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerCountableChain`.
--
--   `BookProof.ChapterEulerCountableChain.one_sub_condCos` (θ : ℕ → ℝ) (n : ℕ) : 1 - condCos θ n = Real.sin (θ n) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerCountableChain.one_sub_condCos`.

-- Generated from ChapterEulerCountableChain.lean — theorem BookProof.ChapterEulerCountableChain.one_sub_condCos
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain


open scoped BigOperators
open Filter Topology

theorem BookProof.ChapterEulerCountableChain.one_sub_condCos (θ : ℕ → ℝ) (n : ℕ) :
    1 - condCos θ n = Real.sin (θ n) ^ 2 := by sorry
