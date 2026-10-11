-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_symm
-- name    : BookProof.ChapterSinusoidalPosition.peInner_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:48:39.425685+00:00
-- url     : https://prove2.me/theorems/7956f151-8915-4eec-96f6-fa15d9bc2c5e
-- title:
--   `BookProof.ChapterSinusoidalPosition.peInner_symm` (w : Fin n → ℝ) (p q : ℝ) : peInner w p q = peInner w q p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.peInner_symm` (w : Fin n → ℝ) (p q : ℝ) : peInner w p q = peInner w q p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.peInner_symm`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.peInner_symm
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

theorem BookProof.ChapterSinusoidalPosition.peInner_symm (w : Fin n → ℝ) (p q : ℝ) : peInner w p q = peInner w q p := by sorry
