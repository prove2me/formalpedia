-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_hasSum_commForm
-- name    : BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.hasSum_commForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T08:11:11.473218+00:00
-- url     : https://prove2.me/theorems/a87314aa-7bb9-4c13-b3ab-876445e68682
-- title:
--   hasSum_commForm
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.hasSum_commForm` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesShiftHamiltonian.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesShiftHamiltonian.lean

-- Generated from ChapterNavierStokesShiftHamiltonian.lean — theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.hasSum_commForm
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

theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.hasSum_commForm (x : maxDom S.sym) :
    HasSum (fun β => 2 * S.step * (S.amp β
        * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
            * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (commForm (shiftH S) (diagMax S.sym) x) := by sorry
