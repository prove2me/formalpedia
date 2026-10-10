-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_polyMom_contract_v
-- name    : BookProof.ChapterGravityPolymomentum.polyMom_contract_v
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:49.224695+00:00
-- url     : https://prove2.me/theorems/c8439bec-fdf4-4cad-8132-e19c92a824bd
-- title:
--   `BookProof.ChapterGravityPolymomentum.polyMom_contract_v` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) : (polyMom e T S Tc u v).mulVec (lower v) = (-e) • (((4 /
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.polyMom_contract_v` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) : (polyMom e T S Tc u v).mulVec (lower v) = (-e) • (((4 / 3) * T) • v + (2 : ℝ) • u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.polyMom_contract_v`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.polyMom_contract_v
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

theorem BookProof.ChapterGravityPolymomentum.polyMom_contract_v (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) :
    (polyMom e T S Tc u v).mulVec (lower v) = (-e) • (((4 / 3) * T) • v + (2 : ℝ) • u) := by sorry
