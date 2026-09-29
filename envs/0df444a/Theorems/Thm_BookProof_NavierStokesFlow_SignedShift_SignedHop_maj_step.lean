-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_maj_step
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_step
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:21:06.106122+00:00
-- url     : https://prove2.me/theorems/1eaba840-bc5a-43fb-be2e-dbdac2a0774c
-- title:
--   : S.maj.step = S.step
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_step` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_step
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_step : S.maj.step = S.step := by sorry
