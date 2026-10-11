-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_self
-- name    : BookProof.ChapterSinusoidalPosition.peInner_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:51:48.827478+00:00
-- url     : https://prove2.me/theorems/701ad492-3051-46e1-89ef-8c9516192587
-- title:
--   `BookProof.ChapterSinusoidalPosition.peInner_self` (w : Fin n → ℝ) (p : ℝ) : peInner w p p = (n : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.peInner_self` (w : Fin n → ℝ) (p : ℝ) : peInner w p p = (n : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.peInner_self`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.peInner_self
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

theorem BookProof.ChapterSinusoidalPosition.peInner_self (w : Fin n → ℝ) (p : ℝ) : peInner w p p = (n : ℝ) := by sorry
