-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_euler_sum_one
-- name    : BookProof.ChapterEulerNState.euler_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:33:42.362526+00:00
-- url     : https://prove2.me/theorems/d9b3dc5d-6b1e-4709-b247-7ea3b9e7d425
-- title:
--   `BookProof.ChapterEulerNState.euler_sum_one` (θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : ∑ k ∈ Finset.range n, bornProb θ n k = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.euler_sum_one` (θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : ∑ k ∈ Finset.range n, bornProb θ n k = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.euler_sum_one`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.euler_sum_one
import Mathlib
import Definitions.Def_ChapterEulerNState
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.euler_sum_one (θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, bornProb θ n k = 1 := by sorry
