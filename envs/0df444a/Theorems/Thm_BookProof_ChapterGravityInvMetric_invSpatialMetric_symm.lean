-- Prove2me | Theorems.Thm_BookProof_ChapterGravityInvMetric_invSpatialMetric_symm
-- name    : BookProof.ChapterGravityInvMetric.invSpatialMetric_symm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:58:17.765364+00:00
-- url     : https://prove2.me/theorems/2e521a54-718e-4d87-9fd6-0b91fe1dac5d
-- title:
--   `BookProof.ChapterGravityInvMetric.invSpatialMetric_symm` (v : Fin 4 → ℝ) : (invSpatialMetric v)ᵀ = invSpatialMetric v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityInvMetric`.
--
--   `BookProof.ChapterGravityInvMetric.invSpatialMetric_symm` (v : Fin 4 → ℝ) : (invSpatialMetric v)ᵀ = invSpatialMetric v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityInvMetric.invSpatialMetric_symm`.

-- Generated from ChapterGravityInvMetric.lean — theorem BookProof.ChapterGravityInvMetric.invSpatialMetric_symm
import Definitions.Def_ChapterGravityMetric
import Mathlib
import Definitions.Def_ChapterGravityInvMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityInvMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

theorem BookProof.ChapterGravityInvMetric.invSpatialMetric_symm (v : Fin 4 → ℝ) :
    (invSpatialMetric v)ᵀ = invSpatialMetric v := by sorry
