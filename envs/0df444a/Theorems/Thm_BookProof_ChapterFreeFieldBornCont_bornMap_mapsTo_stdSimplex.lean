-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornCont_bornMap_mapsTo_stdSimplex
-- name    : BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:32:00.243661+00:00
-- url     : https://prove2.me/theorems/a74db24a-f884-4d0e-a197-c00b7f7debdb
-- title:
--   `BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex` : Set.MapsTo (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (std
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornCont`.
--
--   `BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex` : Set.MapsTo (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex`.

-- Generated from ChapterFreeFieldBornCont.lean — theorem BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
open BookProof.ChapterFreeFieldBornCont

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornCont.bornMap_mapsTo_stdSimplex :
    Set.MapsTo (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n)) := by sorry
