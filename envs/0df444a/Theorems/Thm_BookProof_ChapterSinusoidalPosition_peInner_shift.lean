-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_shift
-- name    : BookProof.ChapterSinusoidalPosition.peInner_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:49:15.92159+00:00
-- url     : https://prove2.me/theorems/82d81568-ff8e-4924-b6e2-44dca2b84113
-- title:
--   `BookProof.ChapterSinusoidalPosition.peInner_shift` (w : Fin n → ℝ) (p q t : ℝ) : peInner w (p + t) (q + t) = peInner w p q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.peInner_shift` (w : Fin n → ℝ) (p q t : ℝ) : peInner w (p + t) (q + t) = peInner w p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.peInner_shift`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.peInner_shift
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

theorem BookProof.ChapterSinusoidalPosition.peInner_shift (w : Fin n → ℝ) (p q t : ℝ) :
    peInner w (p + t) (q + t) = peInner w p q := by sorry
