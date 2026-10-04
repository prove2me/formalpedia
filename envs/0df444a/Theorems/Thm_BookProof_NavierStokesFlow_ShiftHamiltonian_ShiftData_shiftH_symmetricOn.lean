-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_symmetricOn
-- name    : BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T08:25:43.841528+00:00
-- url     : https://prove2.me/theorems/f4a591c6-b1da-499d-ab2e-1e467c354a65
-- title:
--   shiftH_symmetricOn
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_symmetricOn` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesShiftHamiltonian.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesShiftHamiltonian.lean

-- Generated from ChapterNavierStokesShiftHamiltonian.lean — theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian

variable {ι : Type*} (S : ShiftData ι)


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_symmetricOn : SymmetricOn (maxDom S.sym) (shiftH S) := by sorry
