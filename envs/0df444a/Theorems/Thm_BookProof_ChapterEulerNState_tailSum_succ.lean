-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_tailSum_succ
-- name    : BookProof.ChapterEulerNState.tailSum_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:32:39.611023+00:00
-- url     : https://prove2.me/theorems/003f8533-1b6e-4d00-9120-90ba6f10c8be
-- title:
--   `BookProof.ChapterEulerNState.tailSum_succ` (p : ℕ → ℝ) (n k : ℕ) (h : k < n) : tailSum p n k = p k + tailSum p n (k + 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.tailSum_succ` (p : ℕ → ℝ) (n k : ℕ) (h : k < n) : tailSum p n k = p k + tailSum p n (k + 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.tailSum_succ`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.tailSum_succ
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.tailSum_succ (p : ℕ → ℝ) (n k : ℕ) (h : k < n) :
    tailSum p n k = p k + tailSum p n (k + 1) := by sorry
