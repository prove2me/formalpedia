-- Prove2me | Theorems.Thm_BookProof_ChapterRotaryPosition_bornWeightC_rotaryEncode_shift
-- name    : BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:19:53.364982+00:00
-- url     : https://prove2.me/theorems/90c1c702-ef81-4f5a-bda7-96d21dbf8640
-- title:
--   `BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift` (omega : Fin n → ℝ) (a c : ℝ) (pos : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRotaryPosition`.
--
--   `BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift` (omega : Fin n → ℝ) (a c : ℝ) (pos : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC (rotaryEncode omega (a + c) q) (fun l => rotaryEncode omega (pos l + c) (k l)) j = bornWeightC (rotaryEncode omega a q) (fun l => rotaryEncode omega (pos l) (k l)) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift`.

-- Generated from ChapterRotaryPosition.lean — theorem BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

theorem BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift (omega : Fin n → ℝ) (a c : ℝ)
    (pos : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC (rotaryEncode omega (a + c) q)
        (fun l => rotaryEncode omega (pos l + c) (k l)) j
      = bornWeightC (rotaryEncode omega a q) (fun l => rotaryEncode omega (pos l) (k l)) j := by sorry
