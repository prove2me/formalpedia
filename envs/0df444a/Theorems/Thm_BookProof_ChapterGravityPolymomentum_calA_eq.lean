-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_calA_eq
-- name    : BookProof.ChapterGravityPolymomentum.calA_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:47:11.773156+00:00
-- url     : https://prove2.me/theorems/205408db-36f4-4976-964a-ba3bda50c0a9
-- title:
--   `BookProof.ChapterGravityPolymomentum.calA_eq` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) (hSsymm : Sᵀ = S) (hTcanti : Tcᵀ = -Tc) : calA v (polyMom e T S Tc u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.calA_eq` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) (hSsymm : Sᵀ = S) (hTcanti : Tcᵀ = -Tc) : calA v (polyMom e T S Tc u v) = (-2 * e) • Tc
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.calA_eq`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.calA_eq
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

theorem BookProof.ChapterGravityPolymomentum.calA_eq (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hSsymm : Sᵀ = S) (hTcanti : Tcᵀ = -Tc) :
    calA v (polyMom e T S Tc u v) = (-2 * e) • Tc := by sorry
