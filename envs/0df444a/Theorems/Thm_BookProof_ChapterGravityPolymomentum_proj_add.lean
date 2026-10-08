-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_add
-- name    : BookProof.ChapterGravityPolymomentum.proj_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T13:02:26.975991+00:00
-- url     : https://prove2.me/theorems/84fcb827-5269-4709-948c-ee056aa7af44
-- title:
--   `BookProof.ChapterGravityPolymomentum.proj_add` (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) : proj v (M + N) = proj v M + proj v N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.proj_add` (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) : proj v (M + N) = proj v M + proj v N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.proj_add`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.proj_add
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

theorem BookProof.ChapterGravityPolymomentum.proj_add (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (M + N) = proj v M + proj v N := by sorry
