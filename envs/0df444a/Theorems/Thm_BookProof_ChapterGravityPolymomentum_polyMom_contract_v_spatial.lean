-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_polyMom_contract_v_spatial
-- name    : BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:47:38.693883+00:00
-- url     : https://prove2.me/theorems/682fd5bf-c488-4306-b0ab-9f096bdb8119
-- title:
--   `BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) : (spatialProj v).mulVec ((polyMom e T S Tc u v).
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial` (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) : (spatialProj v).mulVec ((polyMom e T S Tc u v).mulVec (lower v)) = (-2 * e) • (spatialProj v).mulVec u
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

theorem BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial (hv : minkSq v = -1) (hS : IsSpatial v S)
    (hTc : IsSpatial v Tc) :
    (spatialProj v).mulVec ((polyMom e T S Tc u v).mulVec (lower v))
      = (-2 * e) • (spatialProj v).mulVec u := by sorry
