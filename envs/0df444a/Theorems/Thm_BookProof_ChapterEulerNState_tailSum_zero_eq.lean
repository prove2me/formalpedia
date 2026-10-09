-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_tailSum_zero_eq
-- name    : BookProof.ChapterEulerNState.tailSum_zero_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:32:44.681803+00:00
-- url     : https://prove2.me/theorems/a1679a45-2540-40c7-8b36-adcb68a7bfb5
-- title:
--   `BookProof.ChapterEulerNState.tailSum_zero_eq` (p : ℕ → ℝ) (n : ℕ) : tailSum p n 0 = ∑ j ∈ Finset.range n, p j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.tailSum_zero_eq` (p : ℕ → ℝ) (n : ℕ) : tailSum p n 0 = ∑ j ∈ Finset.range n, p j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.tailSum_zero_eq`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.tailSum_zero_eq
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.tailSum_zero_eq (p : ℕ → ℝ) (n : ℕ) :
    tailSum p n 0 = ∑ j ∈ Finset.range n, p j := by sorry
