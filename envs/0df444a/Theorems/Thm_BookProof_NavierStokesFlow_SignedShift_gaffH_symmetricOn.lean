-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_gaffH_symmetricOn
-- name    : BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:19:33.243793+00:00
-- url     : https://prove2.me/theorems/1f2ba5b9-2799-4d59-8e12-e99aff302cb0
-- title:
--   : SymmetricOn (maxDom (gsym kap cst)) (gaffH kap cst)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn
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















variable (kap cst : ℝ)

theorem BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn : SymmetricOn (maxDom (gsym kap cst)) (gaffH kap cst) := by sorry
