-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_inner_rotaryEncode_shift
-- name    : BookProof.ChapterRotaryPosition.inner_rotaryEncode_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:47:11.61631+00:00
-- url     : https://prove2.me/theorems/7553a7e2-eeb9-458a-9e00-c0ec01eda313
-- title:
--   `BookProof.ChapterRotaryPosition.inner_rotaryEncode_shift` (omega : Fin n → ℝ) (a b c : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : (inner ℂ (rotaryEncode omega (a + c) q) (rotaryEncode
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.inner_rotaryEncode_shift` (omega : Fin n → ℝ) (a b c : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : (inner ℂ (rotaryEncode omega (a + c) q) (rotaryEncode omega (b + c) k) : ℂ) = inner ℂ (rotaryEncode omega a q) (rotaryEncode omega b k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.inner_rotaryEncode_shift`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.inner_rotaryEncode_shift
import Definitions.Def_ChapterCoherentOverlapComplex
import Mathlib
import Definitions.Def_ChapterRotaryPosition
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.inner_rotaryEncode_shift (omega : Fin n → ℝ) (a b c : ℝ)
    (q k : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (rotaryEncode omega (a + c) q) (rotaryEncode omega (b + c) k) : ℂ)
      = inner ℂ (rotaryEncode omega a q) (rotaryEncode omega b k) := by sorry
