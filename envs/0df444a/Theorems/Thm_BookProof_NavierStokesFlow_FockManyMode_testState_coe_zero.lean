-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_testState_coe_zero
-- name    : BookProof.NavierStokesFlow.FockManyMode.testState_coe_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:17:15.455986+00:00
-- url     : https://prove2.me/theorems/666332b7-0989-4f47-b3c5-a9ff74c96750
-- title:
--   (i₀ : Fin d) : ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) 0 = 1
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.testState_coe_zero` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.testState_coe_zero
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

theorem BookProof.NavierStokesFlow.FockManyMode.testState_coe_zero (i₀ : Fin d) :
    ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) 0 = 1 := by sorry
