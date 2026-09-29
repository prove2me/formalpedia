-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_symmetricOn
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:06:08.957458+00:00
-- url     : https://prove2.me/theorems/29cdb1a9-25da-4b91-aeaf-0b7416621db2
-- title:
--   : SymmetricOn (maxDom sym) (hopH S)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterFarisLavineCore
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open BookProof.FarisLavine
open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn : SymmetricOn (maxDom sym) (hopH S) := by sorry
