-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_relative_bound
-- name    : BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_relative_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T08:11:43.446977+00:00
-- url     : https://prove2.me/theorems/9fa566a8-a8bc-4f68-9e97-7c9d67dc6f3f
-- title:
--   shiftH_relative_bound
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_relative_bound` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesShiftHamiltonian.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesShiftHamiltonian.lean

-- Generated from ChapterNavierStokesShiftHamiltonian.lean — theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian

variable {ι : Type*} (S : ShiftData ι)


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

theorem BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_relative_bound (x : maxDom S.sym) :
    ‖(shiftH S x : L2I ι)‖ ^ 2
      ≤ (1 / 2) * ‖(diagMax S.sym x : L2I ι)‖ ^ 2 + (8 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by sorry
