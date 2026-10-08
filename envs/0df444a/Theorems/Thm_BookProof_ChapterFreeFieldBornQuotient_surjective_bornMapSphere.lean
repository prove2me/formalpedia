-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornQuotient_surjective_bornMapSphere
-- name    : BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T09:51:33.831552+00:00
-- url     : https://prove2.me/theorems/f50a5ccc-7f48-419e-84f5-24c1e19766bc
-- title:
--   `BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere` : Function.Surjective (bornMapSphere n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornQuotient`.
--
--   `BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere` : Function.Surjective (bornMapSphere n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere`.

-- Generated from ChapterFreeFieldBornQuotient.lean — theorem BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Mathlib
import Definitions.Def_ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornQuotient

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont

theorem BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere : Function.Surjective (bornMapSphere n) := by sorry
