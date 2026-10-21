-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_coe
-- name    : BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T23:45:57.985698+00:00
-- url     : https://prove2.me/theorems/ff0aff2e-c3fd-4dbd-b6f1-22ca0efb8314
-- title:
--   The Lean 4 theorem `shiftH_coe` in the `ChapterNavierStokesShiftHamiltonian` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shiftH_coe` in the `ChapterNavierStokesShiftHamiltonian` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesShiftHamiltonian.lean

-- Generated from ChapterNavierStokesShiftHamiltonian.lean — theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
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

theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_coe (x : maxDom S.sym) (β : ι) :
    ((shiftH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β := by sorry
