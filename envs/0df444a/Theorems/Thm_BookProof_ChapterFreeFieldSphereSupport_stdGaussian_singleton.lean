-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldSphereSupport_stdGaussian_singleton
-- name    : BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T04:42:20.600989+00:00
-- url     : https://prove2.me/theorems/8c60c9fe-c3d6-46c9-903f-ba846f9e0c5d
-- title:
--   `BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton` (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) : stdGaussian n {x} = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldSphereSupport`.
--
--   `BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton` (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) : stdGaussian n {x} = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton`.

-- Generated from ChapterFreeFieldSphereSupport.lean — theorem BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Mathlib
import Definitions.Def_ChapterFreeFieldSphereSupport
open BookProof.ChapterFreeFieldSphereSupport

variable {n : ℕ}


open MeasureTheory ProbabilityTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere

theorem BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    stdGaussian n {x} = 0 := by sorry
