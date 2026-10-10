-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_smul
-- name    : BookProof.ChapterGravityPolymomentum.proj_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:45:10.788254+00:00
-- url     : https://prove2.me/theorems/0ea946c8-899a-4df8-85cc-3238ce9bf292
-- title:
--   `BookProof.ChapterGravityPolymomentum.proj_smul` (v : Fin 4 → ℝ) (c : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : proj v (c • M) = c • proj v M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.proj_smul` (v : Fin 4 → ℝ) (c : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : proj v (c • M) = c • proj v M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.proj_smul`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.proj_smul
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

theorem BookProof.ChapterGravityPolymomentum.proj_smul (v : Fin 4 → ℝ) (c : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (c • M) = c • proj v M := by sorry
