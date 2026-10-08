-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_mem_sphere
-- name    : BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:46:28.489986+00:00
-- url     : https://prove2.me/theorems/5dcb90d3-85b4-4fdb-b564-97b12e6df76c
-- title:
--   `BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : bornSection p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSurj`.
--
--   `BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : bornSection p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere`.

-- Generated from ChapterFreeFieldBornSurj.lean — theorem BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere
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

theorem BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    bornSection p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by sorry
