-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex
-- name    : BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:21:25.713215+00:00
-- url     : https://prove2.me/theorems/dc2116de-f095-456c-84d1-8fcdc7ffd4dc
-- title:
--   `BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex` {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : bornMap x ∈ stdSimplex ℝ (Fin n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBorn`.
--
--   `BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex` {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : bornMap x ∈ stdSimplex ℝ (Fin n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex`.

-- Generated from ChapterFreeFieldBorn.lean — theorem BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBorn

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport

theorem BookProof.ChapterFreeFieldBorn.bornMap_mem_stdSimplex {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    bornMap x ∈ stdSimplex ℝ (Fin n) := by sorry
