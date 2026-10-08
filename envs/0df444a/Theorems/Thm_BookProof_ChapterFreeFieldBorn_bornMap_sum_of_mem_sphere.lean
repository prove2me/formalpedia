-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_sum_of_mem_sphere
-- name    : BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:20:58.560184+00:00
-- url     : https://prove2.me/theorems/33d30ce0-c978-40e1-a544-767eb14b4d19
-- title:
--   `BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere` {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ∑ k, bornMap x k = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBorn`.
--
--   `BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere` {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ∑ k, bornMap x k = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere`.

-- Generated from ChapterFreeFieldBorn.lean — theorem BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere
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

theorem BookProof.ChapterFreeFieldBorn.bornMap_sum_of_mem_sphere {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∑ k, bornMap x k = 1 := by sorry
