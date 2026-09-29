-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockSym_nonneg
-- name    : BookProof.NavierStokesFlow.FockManyMode.fockSym_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:07:48.353153+00:00
-- url     : https://prove2.me/theorems/66f60213-70d0-402b-b3a0-c6bfa920a484
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (α : Occ d) : 0 ≤ fockSym κ α
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.fockSym_nonneg` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.fockSym_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockManyMode.fockSym_nonneg (hκ : ∀ i, 0 ≤ κ i) (α : Occ d) : 0 ≤ fockSym κ α := by sorry
