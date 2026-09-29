-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_cons
-- name    : BookProof.NavierStokesFlow.SignedShift.listH_cons
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:23:57.09631+00:00
-- url     : https://prove2.me/theorems/b353e304-fe40-4aed-ae5b-521cc55fdffe
-- title:
--   (S : SignedHop ι sym) (L : List (SignedHop ι sym)) : listH (S :: L) = SignedHop.hopH S + listH L
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.listH_cons` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.listH_cons
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.HermiteFarisLavine









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

theorem BookProof.NavierStokesFlow.SignedShift.listH_cons (S : SignedHop ι sym) (L : List (SignedHop ι sym)) :
    listH (S :: L) = SignedHop.hopH S + listH L := by sorry
