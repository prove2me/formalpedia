-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_testState_coe_eq_zero
-- name    : BookProof.NavierStokesFlow.FockManyMode.testState_coe_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:17:14.807599+00:00
-- url     : https://prove2.me/theorems/e2f17a58-956b-45e9-9c55-4a01e85b3fe7
-- title:
--   (i₀ : Fin d) {β : Occ d} (h0 : β ≠ 0) (h1 : β ≠ modeShift i₀ 0) : ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.testState_coe_eq_zero` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.testState_coe_eq_zero
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

theorem BookProof.NavierStokesFlow.FockManyMode.testState_coe_eq_zero (i₀ : Fin d) {β : Occ d}
    (h0 : β ≠ 0) (h1 : β ≠ modeShift i₀ 0) :
    ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β = 0 := by sorry
