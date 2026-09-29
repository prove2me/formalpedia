-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_commForm_bound
-- name    : BookProof.NavierStokesFlow.SignedShift.listH_commForm_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:18:51.539627+00:00
-- url     : https://prove2.me/theorems/267bd40d-7dae-46e9-98fd-84bfa404a770
-- title:
--   (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) : ∃ cst : ℝ, 0 ≤ cst ∧ ∀ x : maxDom sym, |commForm (listH L) (diagMax sym) x| ≤ cst * quadForm (diagMax sym) x
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.listH_commForm_bound` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.listH_commForm_bound
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

theorem BookProof.NavierStokesFlow.SignedShift.listH_commForm_bound (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) :
    ∃ cst : ℝ, 0 ≤ cst ∧ ∀ x : maxDom sym,
      |commForm (listH L) (diagMax sym) x| ≤ cst * quadForm (diagMax sym) x := by sorry
