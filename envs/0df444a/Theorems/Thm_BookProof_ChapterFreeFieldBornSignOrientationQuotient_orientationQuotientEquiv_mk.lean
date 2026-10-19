-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationQuotient_orientationQuotientEquiv_mk
-- name    : BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:31:47.322212+00:00
-- url     : https://prove2.me/theorems/a47fc9a8-1b8b-4715-921f-9233fe006d93
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk` (n : ℕ) (b : Fin (n + 1) → Bool) : orientationQuotientEquiv n (QuotientAddGroup.mk b) = orientat
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationQuotient`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk` (n : ℕ) (b : Fin (n + 1) → Bool) : orientationQuotientEquiv n (QuotientAddGroup.mk b) = orientationCharacter (n + 1) b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk`.

-- Generated from ChapterFreeFieldBornSignOrientationQuotient.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationQuotient
open BookProof.ChapterFreeFieldBornSignOrientationQuotient


open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

theorem BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk (n : ℕ) (b : Fin (n + 1) → Bool) :
    orientationQuotientEquiv n (QuotientAddGroup.mk b) =
      orientationCharacter (n + 1) b := by sorry
