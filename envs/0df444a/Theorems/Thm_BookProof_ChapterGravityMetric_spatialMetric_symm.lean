-- Prove2me | Theorems.Thm_BookProof_ChapterGravityMetric_spatialMetric_symm
-- name    : BookProof.ChapterGravityMetric.spatialMetric_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:59:36.464875+00:00
-- url     : https://prove2.me/theorems/46b8cf4e-db06-4d30-a728-013d753c07d1
-- title:
--   `BookProof.ChapterGravityMetric.spatialMetric_symm` (v : Fin 4 → ℝ) : (spatialMetric v)ᵀ = spatialMetric v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityMetric`.
--
--   `BookProof.ChapterGravityMetric.spatialMetric_symm` (v : Fin 4 → ℝ) : (spatialMetric v)ᵀ = spatialMetric v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityMetric.spatialMetric_symm`.

-- Generated from ChapterGravityMetric.lean — theorem BookProof.ChapterGravityMetric.spatialMetric_symm
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityMetric.spatialMetric_symm (v : Fin 4 → ℝ) :
    (spatialMetric v)ᵀ = spatialMetric v := by sorry
