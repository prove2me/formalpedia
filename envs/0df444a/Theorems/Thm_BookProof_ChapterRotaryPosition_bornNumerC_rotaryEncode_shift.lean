-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_bornNumerC_rotaryEncode_shift
-- name    : BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:19:39.200377+00:00
-- url     : https://prove2.me/theorems/550c7fdd-82ae-4eda-bc5a-2f0008525c00
-- title:
--   `BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift` (omega : Fin n → ℝ) (a b c : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (rotaryEncode omega (a + c) q) (rotary
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift` (omega : Fin n → ℝ) (a b c : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (rotaryEncode omega (a + c) q) (rotaryEncode omega (b + c) k) = bornNumerC (rotaryEncode omega a q) (rotaryEncode omega b k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift (omega : Fin n → ℝ) (a b c : ℝ)
    (q k : EuclideanSpace ℂ (Fin n)) :
    bornNumerC (rotaryEncode omega (a + c) q) (rotaryEncode omega (b + c) k)
      = bornNumerC (rotaryEncode omega a q) (rotaryEncode omega b k) := by sorry
