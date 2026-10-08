-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornMap_bijOn_nonneg_sphere
-- name    : BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:16:31.953505+00:00
-- url     : https://prove2.me/theorems/a71ebb37-8ee2-4140-9881-73ae81f3e576
-- title:
--   `BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere` : Set.BijOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonneg
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSectionBij`.
--
--   `BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere` : Set.BijOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n) (stdSimplex ℝ (Fin n))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere`.

-- Generated from ChapterFreeFieldBornSectionBij.lean — theorem BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere
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

theorem BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere :
    Set.BijOn (bornMap : EuclideanSpace ℝ (Fin n) → _)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n)
      (stdSimplex ℝ (Fin n)) := by sorry
