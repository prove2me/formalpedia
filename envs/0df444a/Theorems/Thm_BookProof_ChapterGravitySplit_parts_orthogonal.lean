-- Prove2me | Theorems.Thm_BookProof_ChapterGravitySplit_parts_orthogonal
-- name    : BookProof.ChapterGravitySplit.parts_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:51:42.813762+00:00
-- url     : https://prove2.me/theorems/38ff997a-448c-4e80-8030-9e0023b4a13c
-- title:
--   `BookProof.ChapterGravitySplit.parts_orthogonal` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : minkForm (spatialPart v x) (timePart v x) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravitySplit`.
--
--   `BookProof.ChapterGravitySplit.parts_orthogonal` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : minkForm (spatialPart v x) (timePart v x) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravitySplit.parts_orthogonal`.

-- Generated from ChapterGravitySplit.lean — theorem BookProof.ChapterGravitySplit.parts_orthogonal
import Definitions.Def_ChapterGravityTimeProj
import Mathlib
import Definitions.Def_ChapterGravitySplit
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravitySplit



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

theorem BookProof.ChapterGravitySplit.parts_orthogonal (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    minkForm (spatialPart v x) (timePart v x) = 0 := by sorry
