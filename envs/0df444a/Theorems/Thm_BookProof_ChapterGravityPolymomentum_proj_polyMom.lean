-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_polyMom
-- name    : BookProof.ChapterGravityPolymomentum.proj_polyMom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:32.875978+00:00
-- url     : https://prove2.me/theorems/6d79ee0f-fd79-4d71-92aa-b844423cd286
-- title:
--   `BookProof.ChapterGravityPolymomentum.proj_polyMom` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) : proj v (polyMom e T S Tc u v) = e • (S - ((4 / 3) * T) • (met
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.proj_polyMom` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) : proj v (polyMom e T S Tc u v) = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) - Tc)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.proj_polyMom`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.proj_polyMom
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

theorem BookProof.ChapterGravityPolymomentum.proj_polyMom (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) :
    proj v (polyMom e T S Tc u v)
      = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) - Tc) := by sorry
