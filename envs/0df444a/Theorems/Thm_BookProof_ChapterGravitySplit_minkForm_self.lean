-- Prove2me | Theorems.Thm_BookProof_ChapterGravitySplit_minkForm_self
-- name    : BookProof.ChapterGravitySplit.minkForm_self
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:27.720503+00:00
-- url     : https://prove2.me/theorems/cd69163c-23a9-4f8a-990f-a65e5a14ca70
-- title:
--   `BookProof.ChapterGravitySplit.minkForm_self` (x : Fin 4 → ℝ) : minkForm x x = minkSq x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravitySplit`.
--
--   `BookProof.ChapterGravitySplit.minkForm_self` (x : Fin 4 → ℝ) : minkForm x x = minkSq x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravitySplit.minkForm_self`.

-- Generated from ChapterGravitySplit.lean — theorem BookProof.ChapterGravitySplit.minkForm_self
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

theorem BookProof.ChapterGravitySplit.minkForm_self (x : Fin 4 → ℝ) : minkForm x x = minkSq x := by sorry
