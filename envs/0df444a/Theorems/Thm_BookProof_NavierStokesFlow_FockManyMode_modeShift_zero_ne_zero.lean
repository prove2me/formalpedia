-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_modeShift_zero_ne_zero
-- name    : BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:10:41.017026+00:00
-- url     : https://prove2.me/theorems/5ac2ffbd-f40d-45c1-aa80-38edf970683d
-- title:
--   (i : Fin d) : modeShift i (0 : Occ d) ≠ 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_ne_zero` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_ne_zero (i : Fin d) : modeShift i (0 : Occ d) ≠ 0 := by sorry
