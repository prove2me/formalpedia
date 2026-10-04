-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_commForm_fockH
-- name    : BookProof.NavierStokesFlow.FockManyMode.commForm_fockH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:50:38.185426+00:00
-- url     : https://prove2.me/theorems/a027891d-5e6c-4d85-81ce-39e181ddcab8
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) : commForm (fockH hκ) (diagMax (fockSym κ)) x = ∑ i, commForm (ShiftData.shiftH (modeData hκ i)) (diagMax (fockSym κ)) x
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.commForm_fockH` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.commForm_fockH
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

theorem BookProof.NavierStokesFlow.FockManyMode.commForm_fockH (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    commForm (fockH hκ) (diagMax (fockSym κ)) x
      = ∑ i, commForm (ShiftData.shiftH (modeData hκ i)) (diagMax (fockSym κ)) x := by sorry
