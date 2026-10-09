-- Prove2me | Theorems.Thm_BookProof_ChapterGravitySplit_minkForm_comm
-- name    : BookProof.ChapterGravitySplit.minkForm_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:51:00.99389+00:00
-- url     : https://prove2.me/theorems/f5b72233-05d9-4dec-9aa0-1045b9643fdc
-- title:
--   `BookProof.ChapterGravitySplit.minkForm_comm` (x y : Fin 4 → ℝ) : minkForm x y = minkForm y x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravitySplit`.
--
--   `BookProof.ChapterGravitySplit.minkForm_comm` (x y : Fin 4 → ℝ) : minkForm x y = minkForm y x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravitySplit.minkForm_comm`.

-- Generated from ChapterGravitySplit.lean — theorem BookProof.ChapterGravitySplit.minkForm_comm
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

theorem BookProof.ChapterGravitySplit.minkForm_comm (x y : Fin 4 → ℝ) : minkForm x y = minkForm y x := by sorry
