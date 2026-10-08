-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_surjOn_stdSimplex
-- name    : BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:09:13.070722+00:00
-- url     : https://prove2.me/theorems/0cb96180-00f2-401a-a5f1-b9f2b41fb69e
-- title:
--   `BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex` : Set.SurjOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSurj`.
--
--   `BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex` : Set.SurjOn (bornMap : EuclideanSpace ℝ (Fin n) → _) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex`.

-- Generated from ChapterFreeFieldBornSurj.lean — theorem BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornSurj

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn

theorem BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex :
    Set.SurjOn (bornMap : EuclideanSpace ℝ (Fin n) → _)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n)) := by sorry
