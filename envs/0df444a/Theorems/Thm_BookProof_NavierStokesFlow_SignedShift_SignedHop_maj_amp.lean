-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_maj_amp
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_amp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:19:44.670259+00:00
-- url     : https://prove2.me/theorems/6edefe33-045f-44bc-9de9-a02f68d39933
-- title:
--   : S.maj.amp = S.bnd
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_amp` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_amp
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_amp : S.maj.amp = S.bnd := by sorry
