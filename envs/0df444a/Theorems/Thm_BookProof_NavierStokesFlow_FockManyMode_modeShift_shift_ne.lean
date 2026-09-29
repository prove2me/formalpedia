-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_modeShift_shift_ne
-- name    : BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:09:11.992054+00:00
-- url     : https://prove2.me/theorems/c4c00320-1e69-492d-aa00-cb6a8784a2b5
-- title:
--   (i i₀ : Fin d) : modeShift i (modeShift i₀ (0 : Occ d)) ≠ 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne (i i₀ : Fin d) :
    modeShift i (modeShift i₀ (0 : Occ d)) ≠ 0 := by sorry
