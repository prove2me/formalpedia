-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_tailSum_nonneg
-- name    : BookProof.ChapterEulerNState.tailSum_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:33:22.565688+00:00
-- url     : https://prove2.me/theorems/ae14c67e-cd05-4b3c-bf1d-9408943568e8
-- title:
--   `BookProof.ChapterEulerNState.tailSum_nonneg` (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (n k : ℕ) : 0 ≤ tailSum p n k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.tailSum_nonneg` (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (n k : ℕ) : 0 ≤ tailSum p n k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.tailSum_nonneg`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.tailSum_nonneg
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.tailSum_nonneg (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (n k : ℕ) :
    0 ≤ tailSum p n k := by sorry
