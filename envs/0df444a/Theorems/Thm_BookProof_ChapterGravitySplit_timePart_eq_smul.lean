-- Prove2me | Theorems.Thm_BookProof_ChapterGravitySplit_timePart_eq_smul
-- name    : BookProof.ChapterGravitySplit.timePart_eq_smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:51:11.512182+00:00
-- url     : https://prove2.me/theorems/f864417a-82c1-4275-9059-bca23ecfb8c9
-- title:
--   `BookProof.ChapterGravitySplit.timePart_eq_smul` (v x : Fin 4 → ℝ) : timePart v x = (-(minkForm x v)) • v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravitySplit`.
--
--   `BookProof.ChapterGravitySplit.timePart_eq_smul` (v x : Fin 4 → ℝ) : timePart v x = (-(minkForm x v)) • v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravitySplit.timePart_eq_smul`.

-- Generated from ChapterGravitySplit.lean — theorem BookProof.ChapterGravitySplit.timePart_eq_smul
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

theorem BookProof.ChapterGravitySplit.timePart_eq_smul (v x : Fin 4 → ℝ) :
    timePart v x = (-(minkForm x v)) • v := by sorry
