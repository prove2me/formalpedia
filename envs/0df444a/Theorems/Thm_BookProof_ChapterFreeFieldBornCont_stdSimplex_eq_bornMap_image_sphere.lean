-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornCont_stdSimplex_eq_bornMap_image_sphere
-- name    : BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:32:09.116007+00:00
-- url     : https://prove2.me/theorems/66da3c34-8325-4b5f-b227-dd53fdfa05d1
-- title:
--   `BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere` : stdSimplex ℝ (Fin n) = (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' (Metric.sphere (0 : Euclidean
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornCont`.
--
--   `BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere` : stdSimplex ℝ (Fin n) = (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere`.

-- Generated from ChapterFreeFieldBornCont.lean — theorem BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
open BookProof.ChapterFreeFieldBornCont

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere :
    stdSimplex ℝ (Fin n) =
      (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ''
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by sorry
