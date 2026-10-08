-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornQuotient_continuous_bornMapSphere
-- name    : BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T09:51:34.64957+00:00
-- url     : https://prove2.me/theorems/cb303e66-06e2-44de-aa73-22899dc1bd57
-- title:
--   `BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere` : Continuous (bornMapSphere n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornQuotient`.
--
--   `BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere` : Continuous (bornMapSphere n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere`.

-- Generated from ChapterFreeFieldBornQuotient.lean — theorem BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere
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

theorem BookProof.ChapterFreeFieldBornQuotient.continuous_bornMapSphere : Continuous (bornMapSphere n) := by sorry
