-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_calP_eq
-- name    : BookProof.ChapterGravityPolymomentum.calP_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:47:19.658985+00:00
-- url     : https://prove2.me/theorems/e537ee4c-cfad-45e0-a104-91e67aa7a093
-- title:
--   `BookProof.ChapterGravityPolymomentum.calP_eq` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) : calP
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.calP_eq` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) : calP v (polyMom e T S Tc u v) = -4 * e * T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.calP_eq`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.calP_eq
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

theorem BookProof.ChapterGravityPolymomentum.calP_eq (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) :
    calP v (polyMom e T S Tc u v) = -4 * e * T := by sorry
