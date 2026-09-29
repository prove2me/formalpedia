-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_modeShift_zero_inj
-- name    : BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_inj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:09:56.605003+00:00
-- url     : https://prove2.me/theorems/7ffb70ef-0698-45fa-bfec-efdb025837e4
-- title:
--   {i j : Fin d} (h : modeShift i (0 : Occ d) = modeShift j 0) : i = j
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_inj` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_inj
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_zero_inj {i j : Fin d} (h : modeShift i (0 : Occ d) = modeShift j 0) :
    i = j := by sorry
