-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornQuotient_isQuotientMap_bornMapSphere
-- name    : BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T09:52:31.473977+00:00
-- url     : https://prove2.me/theorems/8164b784-78b8-4d58-8579-fee9042ce865
-- title:
--   `BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere` : Topology.IsQuotientMap (bornMapSphere n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornQuotient`.
--
--   `BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere` : Topology.IsQuotientMap (bornMapSphere n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere`.

-- Generated from ChapterFreeFieldBornQuotient.lean — theorem BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere
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

theorem BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere :
    Topology.IsQuotientMap (bornMapSphere n) := by sorry
