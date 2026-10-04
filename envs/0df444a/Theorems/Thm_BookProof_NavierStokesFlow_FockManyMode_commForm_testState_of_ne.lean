-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_commForm_testState_of_ne
-- name    : BookProof.NavierStokesFlow.FockManyMode.commForm_testState_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:17:49.035861+00:00
-- url     : https://prove2.me/theorems/2bebcbb7-9db5-4b21-9727-22cf5a67522f
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) {i i₀ : Fin d} (hne : i ≠ i₀) : commForm (ShiftData.shiftH (modeData hκ i)) (diagMax (fockSym κ)) (testState κ i₀) = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.commForm_testState_of_ne` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.commForm_testState_of_ne
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.commForm_testState_of_ne (hκ : ∀ i, 0 ≤ κ i) {i i₀ : Fin d} (hne : i ≠ i₀) :
    commForm (ShiftData.shiftH (modeData hκ i)) (diagMax (fockSym κ)) (testState κ i₀) = 0 := by sorry
