-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldSphereSupport_normalize_mem_sphere
-- name    : BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T04:42:10.235561+00:00
-- url     : https://prove2.me/theorems/c600e80c-5093-4705-9076-bdd35eb74f4a
-- title:
--   `BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere` {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : normalize x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldSphereSupport`.
--
--   `BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere` {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : normalize x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere`.

-- Generated from ChapterFreeFieldSphereSupport.lean — theorem BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Mathlib
import Definitions.Def_ChapterFreeFieldSphereSupport
open BookProof.ChapterFreeFieldSphereSupport

variable {n : ℕ}


open MeasureTheory ProbabilityTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere

theorem BookProof.ChapterFreeFieldSphereSupport.normalize_mem_sphere {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    normalize x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by sorry
