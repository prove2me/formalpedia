-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_maj_sym
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_sym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:21:47.064087+00:00
-- url     : https://prove2.me/theorems/bd8028e7-94f7-4ecb-bf78-f8fbe2d40c0c
-- title:
--   : S.maj.sym = sym
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_sym` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_sym
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.maj_sym : S.maj.sym = sym := by sorry
