-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_nullElt_mul
-- name    : BookProof.ChapterWignerLittleGroup.nullElt_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:01.678981+00:00
-- url     : https://prove2.me/theorems/4f8ba7e4-39e3-4514-afd2-cf355dc8e11d
-- title:
--   `BookProof.ChapterWignerLittleGroup.nullElt_mul` (a b a' b' : ℂ) : nullElt a b * nullElt a' b' = nullElt (a * a') (a * b' + b * (starRingEnd ℂ) a')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.nullElt_mul` (a b a' b' : ℂ) : nullElt a b * nullElt a' b' = nullElt (a * a') (a * b' + b * (starRingEnd ℂ) a')
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.nullElt_mul`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.nullElt_mul
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.nullElt_mul (a b a' b' : ℂ) :
    nullElt a b * nullElt a' b' = nullElt (a * a') (a * b' + b * (starRingEnd ℂ) a') := by sorry
