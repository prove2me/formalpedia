-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_commForm_bound
-- name    : BookProof.NavierStokesFlow.FockManyMode.fockH_commForm_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:16:46.490061+00:00
-- url     : https://prove2.me/theorems/1ec1a86e-b7c5-4fb9-92dd-baf13efed005
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) : |commForm (fockH hκ) (diagMax (fockSym κ)) x| ≤ (∑ i, (2 * κ i + 4 * κ i ^ 2)) * quadForm (diagMax (fockSym κ)) x
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.fockH_commForm_bound` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.fockH_commForm_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.fockH_commForm_bound (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    |commForm (fockH hκ) (diagMax (fockSym κ)) x|
      ≤ (∑ i, (2 * κ i + 4 * κ i ^ 2)) * quadForm (diagMax (fockSym κ)) x := by sorry
