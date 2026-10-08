-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornMap_injOn_nonneg
-- name    : BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:57:25.060478+00:00
-- url     : https://prove2.me/theorems/3bfc8f03-a54f-4259-a7a6-174bb08df77d
-- title:
--   `BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg` : Set.InjOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (nonnegOrthant n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSectionBij`.
--
--   `BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg` : Set.InjOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (nonnegOrthant n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg`.

-- Generated from ChapterFreeFieldBornSectionBij.lean — theorem BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornSectionBij

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornSectionBij.bornMap_injOn_nonneg :
    Set.InjOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (nonnegOrthant n) := by sorry
