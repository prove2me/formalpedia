-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_tailSum_last
-- name    : BookProof.ChapterEulerNState.tailSum_last
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:35:34.665665+00:00
-- url     : https://prove2.me/theorems/334ed598-d5bf-4840-9e13-e7a670f78125
-- title:
--   `BookProof.ChapterEulerNState.tailSum_last` (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : tailSum p n (n - 1) = p (n - 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.tailSum_last` (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : tailSum p n (n - 1) = p (n - 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.tailSum_last`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.tailSum_last
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.tailSum_last (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    tailSum p n (n - 1) = p (n - 1) := by sorry
