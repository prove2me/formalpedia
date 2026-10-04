-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_commForm_testState_self
-- name    : BookProof.NavierStokesFlow.FockManyMode.commForm_testState_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:18:12.868116+00:00
-- url     : https://prove2.me/theorems/a1ed0741-2ee7-4a78-9567-11cbedfc6309
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (i₀ : Fin d) : commForm (ShiftData.shiftH (modeData hκ i₀)) (diagMax (fockSym κ)) (testState κ i₀) = 2 * (4 * κ i₀) * modeAmp κ i₀ 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.commForm_testState_self` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.commForm_testState_self
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

theorem BookProof.NavierStokesFlow.FockManyMode.commForm_testState_self (hκ : ∀ i, 0 ≤ κ i) (i₀ : Fin d) :
    commForm (ShiftData.shiftH (modeData hκ i₀)) (diagMax (fockSym κ)) (testState κ i₀)
      = 2 * (4 * κ i₀) * modeAmp κ i₀ 0 := by sorry
