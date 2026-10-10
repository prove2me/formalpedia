-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_inner_rotaryEncode
-- name    : BookProof.ChapterRotaryPosition.inner_rotaryEncode
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:46:54.513966+00:00
-- url     : https://prove2.me/theorems/ccd40205-e7c4-4634-9c22-1ed3044aed7a
-- title:
--   `BookProof.ChapterRotaryPosition.inner_rotaryEncode` (omega : Fin n → ℝ) (a b : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : (inner ℂ (rotaryEncode omega a q) (rotaryEncode omega b k) : ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.inner_rotaryEncode` (omega : Fin n → ℝ) (a b : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : (inner ℂ (rotaryEncode omega a q) (rotaryEncode omega b k) : ℂ) = inner ℂ q (rotaryEncode omega (b - a) k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.inner_rotaryEncode`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.inner_rotaryEncode
import Definitions.Def_ChapterCoherentOverlapComplex
import Mathlib
import Definitions.Def_ChapterRotaryPosition
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.inner_rotaryEncode (omega : Fin n → ℝ) (a b : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (rotaryEncode omega a q) (rotaryEncode omega b k) : ℂ)
      = inner ℂ q (rotaryEncode omega (b - a) k) := by sorry
