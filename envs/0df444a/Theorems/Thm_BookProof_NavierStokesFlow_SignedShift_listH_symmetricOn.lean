-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_symmetricOn
-- name    : BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:13:14.761794+00:00
-- url     : https://prove2.me/theorems/450aeed2-622d-4d2a-8c24-742aa0a626b7
-- title:
--   (L : List (SignedHop ι sym)) : SymmetricOn (maxDom sym) (listH L)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterFarisLavineCore
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.HermiteFarisLavine









open BookProof.FarisLavine
open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

theorem BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn (L : List (SignedHop ι sym)) : SymmetricOn (maxDom sym) (listH L) := by sorry
