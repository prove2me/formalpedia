-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_rotaryEncode_add
-- name    : BookProof.ChapterRotaryPosition.rotaryEncode_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:47:06.847311+00:00
-- url     : https://prove2.me/theorems/914e947a-7ec0-4ffd-ba1c-26e23f331a8f
-- title:
--   `BookProof.ChapterRotaryPosition.rotaryEncode_add` (omega : Fin n → ℝ) (p p' : ℝ) (q : EuclideanSpace ℂ (Fin n)) : rotaryEncode omega (p + p') q = rotaryEncode omega p (rotaryEncod
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.rotaryEncode_add` (omega : Fin n → ℝ) (p p' : ℝ) (q : EuclideanSpace ℂ (Fin n)) : rotaryEncode omega (p + p') q = rotaryEncode omega p (rotaryEncode omega p' q)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.rotaryEncode_add`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.rotaryEncode_add
import Definitions.Def_ChapterCoherentOverlapComplex
import Mathlib
import Definitions.Def_ChapterRotaryPosition
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.rotaryEncode_add (omega : Fin n → ℝ) (p p' : ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    rotaryEncode omega (p + p') q = rotaryEncode omega p (rotaryEncode omega p' q) := by sorry
