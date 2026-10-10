-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_coherentOverlapC_rotaryEncode
-- name    : BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:19:31.250993+00:00
-- url     : https://prove2.me/theorems/3cf3ca43-0247-4c2d-86a9-0fb49122693e
-- title:
--   `BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode` (omega : Fin n → ℝ) (a b : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC (rotaryEncode omega a q) (rotaryEn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode` (omega : Fin n → ℝ) (a b : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC (rotaryEncode omega a q) (rotaryEncode omega b k) = coherentOverlapC q (rotaryEncode omega (b - a) k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode (omega : Fin n → ℝ) (a b : ℝ)
    (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC (rotaryEncode omega a q) (rotaryEncode omega b k)
      = coherentOverlapC q (rotaryEncode omega (b - a) k) := by sorry
