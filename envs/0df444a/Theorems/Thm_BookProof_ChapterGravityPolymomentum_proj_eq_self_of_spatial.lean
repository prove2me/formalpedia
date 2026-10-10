-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_eq_self_of_spatial
-- name    : BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:45:30.936657+00:00
-- url     : https://prove2.me/theorems/5275873a-e35e-4653-9350-f019e2a6e009
-- title:
--   `BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial` (v : Fin 4 → ℝ) {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSpatial v M) : proj v M = M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial` (v : Fin 4 → ℝ) {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSpatial v M) : proj v M = M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial
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

theorem BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial (v : Fin 4 → ℝ) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : IsSpatial v M) : proj v M = M := by sorry
