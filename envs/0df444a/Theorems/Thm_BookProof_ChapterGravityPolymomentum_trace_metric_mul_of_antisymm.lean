-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_trace_metric_mul_of_antisymm
-- name    : BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:46:58.819983+00:00
-- url     : https://prove2.me/theorems/041f2794-ef6d-4888-886b-344997d87c77
-- title:
--   `BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm` {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Mᵀ = -M) : (metric * M).trace = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm` {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Mᵀ = -M) : (metric * M).trace = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Mᵀ = -M) :
    (metric * M).trace = 0 := by sorry
