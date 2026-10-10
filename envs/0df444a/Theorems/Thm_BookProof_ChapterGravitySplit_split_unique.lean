-- Prove2me | Theorems.Thm_BookProof_ChapterGravitySplit_split_unique
-- name    : BookProof.ChapterGravitySplit.split_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:51:40.560975+00:00
-- url     : https://prove2.me/theorems/a4724561-1bfd-4e69-8a34-58b4b45b45dd
-- title:
--   `BookProof.ChapterGravitySplit.split_unique` (v x s : Fin 4 → ℝ) (c : ℝ) (hv : minkSq v = -1) (hs : minkForm s v = 0) (hx : x = s + c • v) : s = spatialPart v x ∧ c • v = timePart
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravitySplit`.
--
--   `BookProof.ChapterGravitySplit.split_unique` (v x s : Fin 4 → ℝ) (c : ℝ) (hv : minkSq v = -1) (hs : minkForm s v = 0) (hx : x = s + c • v) : s = spatialPart v x ∧ c • v = timePart v x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravitySplit.split_unique`.

-- Generated from ChapterGravitySplit.lean — theorem BookProof.ChapterGravitySplit.split_unique
import Mathlib
import Definitions.Def_ChapterGravitySplit
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj
open BookProof.ChapterGravitySplit



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

theorem BookProof.ChapterGravitySplit.split_unique (v x s : Fin 4 → ℝ) (c : ℝ) (hv : minkSq v = -1)
    (hs : minkForm s v = 0) (hx : x = s + c • v) :
    s = spatialPart v x ∧ c • v = timePart v x := by sorry
