-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_nullElt_conj_translation
-- name    : BookProof.ChapterWignerLittleGroup.nullElt_conj_translation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:30.531567+00:00
-- url     : https://prove2.me/theorems/65d631a5-2c39-4e39-8dd2-69e9e0997a1f
-- title:
--   `BookProof.ChapterWignerLittleGroup.nullElt_conj_translation` (a b : ℂ) (ha : a * (starRingEnd ℂ) a = 1) : nullElt a 0 * nullElt 1 b * nullElt ((starRingEnd ℂ) a) 0 = nullElt 1 (a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.nullElt_conj_translation` (a b : ℂ) (ha : a * (starRingEnd ℂ) a = 1) : nullElt a 0 * nullElt 1 b * nullElt ((starRingEnd ℂ) a) 0 = nullElt 1 (a * a * b)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.nullElt_conj_translation`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.nullElt_conj_translation
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.nullElt_conj_translation (a b : ℂ) (ha : a * (starRingEnd ℂ) a = 1) :
    nullElt a 0 * nullElt 1 b * nullElt ((starRingEnd ℂ) a) 0 = nullElt 1 (a * a * b) := by sorry
