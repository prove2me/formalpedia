-- Prove2me | Theorems.Thm_BookProof_ChapterGravityInvMetric_invSpatialMetric_mulVec_lower_self
-- name    : BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:59:52.130742+00:00
-- url     : https://prove2.me/theorems/172e6260-58ba-45c9-bc74-fe8c5aaaaece
-- title:
--   `BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (invSpatialMetric v).mulVec (lower v) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityInvMetric`.
--
--   `BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (invSpatialMetric v).mulVec (lower v) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self`.

-- Generated from ChapterGravityInvMetric.lean — theorem BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self
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

theorem BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (invSpatialMetric v).mulVec (lower v) = 0 := by sorry
