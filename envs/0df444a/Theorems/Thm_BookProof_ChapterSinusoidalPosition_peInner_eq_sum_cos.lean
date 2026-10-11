-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_eq_sum_cos
-- name    : BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:48:26.334188+00:00
-- url     : https://prove2.me/theorems/f32c9504-016c-4624-9402-973a552acb6c
-- title:
--   `BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos` (w : Fin n → ℝ) (p q : ℝ) : peInner w p q = ∑ a, Real.cos (w a * (p - q))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos` (w : Fin n → ℝ) (p q : ℝ) : peInner w p q = ∑ a, Real.cos (w a * (p - q))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

theorem BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos (w : Fin n → ℝ) (p q : ℝ) :
    peInner w p q = ∑ a, Real.cos (w a * (p - q)) := by sorry
