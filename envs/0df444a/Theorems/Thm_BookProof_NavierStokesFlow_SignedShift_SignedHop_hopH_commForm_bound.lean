-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_commForm_bound
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_commForm_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:12:32.013063+00:00
-- url     : https://prove2.me/theorems/1a3e8d7b-0e18-43f4-86d4-6a1f0a314069
-- title:
--   (x : maxDom sym) : |commForm (hopH S) (diagMax sym) x| ≤ (2 * S.step * (1 / 4 + S.K)) * quadForm (diagMax sym) x
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_commForm_bound` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_commForm_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_commForm_bound (x : maxDom sym) :
    |commForm (hopH S) (diagMax sym) x|
      ≤ (2 * S.step * (1 / 4 + S.K)) * quadForm (diagMax sym) x := by sorry
