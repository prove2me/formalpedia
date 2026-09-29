-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_summable_crossA
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:48:01.732855+00:00
-- url     : https://prove2.me/theorems/5bb8228d-5add-41ff-951c-1f6e4ec47982
-- title:
--   {X Y : ι → ℂ} (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) : Summable (S.crossA X Y)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossA` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossA
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossA {X Y : ι → ℂ}
    (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) :
    Summable (S.crossA X Y) := by sorry
