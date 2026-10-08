-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_trace_vecMulVec
-- name    : BookProof.ChapterGravityPolymomentum.trace_vecMulVec
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T13:01:51.518395+00:00
-- url     : https://prove2.me/theorems/2b9ee9ae-75e5-4897-9838-fabeb84af530
-- title:
--   `BookProof.ChapterGravityPolymomentum.trace_vecMulVec` (w u : Fin 4 → ℝ) : (vecMulVec w u).trace = ∑ a, w a * u a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.trace_vecMulVec` (w u : Fin 4 → ℝ) : (vecMulVec w u).trace = ∑ a, w a * u a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.trace_vecMulVec`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.trace_vecMulVec
import Definitions.Def_ChapterGravityProjector
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.trace_vecMulVec (w u : Fin 4 → ℝ) :
    (vecMulVec w u).trace = ∑ a, w a * u a := by sorry
