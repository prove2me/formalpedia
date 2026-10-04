-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_testState_coe
-- name    : BookProof.NavierStokesFlow.FockManyMode.testState_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:51:08.711388+00:00
-- url     : https://prove2.me/theorems/4c3b962f-0d7e-44d4-a281-d2f2bb51924d
-- title:
--   (i₀ : Fin d) (β : Occ d) : ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β = if β = 0 then 1 else if β = modeShift i₀ 0 then 1 else 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.testState_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.testState_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.testState_coe (i₀ : Fin d) (β : Occ d) :
    ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β
      = if β = 0 then 1 else if β = modeShift i₀ 0 then 1 else 0 := by sorry
