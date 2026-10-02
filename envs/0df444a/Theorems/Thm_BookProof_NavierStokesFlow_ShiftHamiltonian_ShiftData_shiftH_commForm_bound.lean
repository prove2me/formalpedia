-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_commForm_bound
-- name    : BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_commForm_bound
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T08:11:41.604389+00:00
-- url     : https://prove2.me/theorems/f2de434b-6c65-4607-a472-00c0d5c74fd9
-- title:
--   shiftH_commForm_bound
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_commForm_bound` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesShiftHamiltonian.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesShiftHamiltonian.lean

-- Generated from ChapterNavierStokesShiftHamiltonian.lean — theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_commForm_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian

variable {ι : Type*} (S : ShiftData ι)


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_commForm_bound (x : maxDom S.sym) :
    |commForm (shiftH S) (diagMax S.sym) x|
      ≤ (2 * S.step * (1 / 4 + S.K)) * quadForm (diagMax S.sym) x := by sorry
