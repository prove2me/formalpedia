-- Prove2me | Theorems.Thm_BookProof_ChapterGravitySplit_spatialPart_orthogonal
-- name    : BookProof.ChapterGravitySplit.spatialPart_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:51:27.970922+00:00
-- url     : https://prove2.me/theorems/9e34942e-9dcf-4f7c-a2dc-feeba6537266
-- title:
--   `BookProof.ChapterGravitySplit.spatialPart_orthogonal` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : minkForm (spatialPart v x) v = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravitySplit`.
--
--   `BookProof.ChapterGravitySplit.spatialPart_orthogonal` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : minkForm (spatialPart v x) v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravitySplit.spatialPart_orthogonal`.

-- Generated from ChapterGravitySplit.lean — theorem BookProof.ChapterGravitySplit.spatialPart_orthogonal
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

theorem BookProof.ChapterGravitySplit.spatialPart_orthogonal (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    minkForm (spatialPart v x) v = 0 := by sorry
