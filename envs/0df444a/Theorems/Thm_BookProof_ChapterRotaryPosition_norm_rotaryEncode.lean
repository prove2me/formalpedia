-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_norm_rotaryEncode
-- name    : BookProof.ChapterRotaryPosition.norm_rotaryEncode
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:46:40.300467+00:00
-- url     : https://prove2.me/theorems/317a633c-813b-4114-9799-3a1f1f2533fa
-- title:
--   `BookProof.ChapterRotaryPosition.norm_rotaryEncode` (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n)) : ‖rotaryEncode omega p q‖ = ‖q‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.norm_rotaryEncode` (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n)) : ‖rotaryEncode omega p q‖ = ‖q‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.norm_rotaryEncode`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.norm_rotaryEncode
import Definitions.Def_ChapterCoherentOverlapComplex
import Mathlib
import Definitions.Def_ChapterRotaryPosition
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.norm_rotaryEncode (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    ‖rotaryEncode omega p q‖ = ‖q‖ := by sorry
