-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_modeShift_shift_ne_prime
-- name    : BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T08:47:40.488972+00:00
-- url     : https://prove2.me/theorems/ded0fe3f-bdc3-46d0-9ef2-210dbea1499e
-- title:
--   modeShift_shift_ne'
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne'` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesFockManyMode.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockManyMode.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne'
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne_prime (i i₀ : Fin d) :
    modeShift i (modeShift i₀ (0 : Occ d)) ≠ modeShift i₀ 0 := by sorry
