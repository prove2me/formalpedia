-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_calS_eq
-- name    : BookProof.ChapterGravityPolymomentum.calS_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:47:27.69881+00:00
-- url     : https://prove2.me/theorems/435eee20-acea-4055-8ec4-c44e4762f782
-- title:
--   `BookProof.ChapterGravityPolymomentum.calS_eq` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) (hSsymm : Sᵀ = S) (hStraceless : (metric * S).trace = 0) (hTcanti :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.calS_eq` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) (hSsymm : Sᵀ = S) (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) : calS v (polyMom e T S Tc u v) = (2 * e) • S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.calS_eq`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.calS_eq
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

theorem BookProof.ChapterGravityPolymomentum.calS_eq (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hSsymm : Sᵀ = S) (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) :
    calS v (polyMom e T S Tc u v) = (2 * e) • S := by sorry
