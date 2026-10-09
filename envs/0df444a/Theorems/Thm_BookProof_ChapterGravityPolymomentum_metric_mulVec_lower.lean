-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_mulVec_lower
-- name    : BookProof.ChapterGravityPolymomentum.metric_mulVec_lower
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:01:43.192887+00:00
-- url     : https://prove2.me/theorems/4850c5d8-0004-4413-b412-59f0c85dfc34
-- title:
--   `BookProof.ChapterGravityPolymomentum.metric_mulVec_lower` (v : Fin 4 → ℝ) : metric.mulVec (lower v) = v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.metric_mulVec_lower` (v : Fin 4 → ℝ) : metric.mulVec (lower v) = v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.metric_mulVec_lower`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.metric_mulVec_lower
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.metric_mulVec_lower (v : Fin 4 → ℝ) : metric.mulVec (lower v) = v := by sorry
