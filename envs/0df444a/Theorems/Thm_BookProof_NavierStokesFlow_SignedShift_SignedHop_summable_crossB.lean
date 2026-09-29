-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_summable_crossB
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossB
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:48:40.145598+00:00
-- url     : https://prove2.me/theorems/4730007b-b137-4f8c-839b-8c1ebf25a701
-- title:
--   {X Y : ι → ℂ} (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) : Summable (S.crossB X Y)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossB` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossB
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossB {X Y : ι → ℂ}
    (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) :
    Summable (S.crossB X Y) := by sorry
