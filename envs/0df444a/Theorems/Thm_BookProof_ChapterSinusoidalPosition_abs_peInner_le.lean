-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_abs_peInner_le
-- name    : BookProof.ChapterSinusoidalPosition.abs_peInner_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:49:43.575653+00:00
-- url     : https://prove2.me/theorems/0e91ff30-b256-41d5-81b4-fd7c2433458f
-- title:
--   `BookProof.ChapterSinusoidalPosition.abs_peInner_le` (w : Fin n → ℝ) (p q : ℝ) : |peInner w p q| ≤ (n : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.abs_peInner_le` (w : Fin n → ℝ) (p q : ℝ) : |peInner w p q| ≤ (n : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.abs_peInner_le`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.abs_peInner_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

theorem BookProof.ChapterSinusoidalPosition.abs_peInner_le (w : Fin n → ℝ) (p q : ℝ) : |peInner w p q| ≤ (n : ℝ) := by sorry
