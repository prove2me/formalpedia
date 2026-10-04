-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_relative_bound
-- name    : BookProof.NavierStokesFlow.FockManyMode.fockH_relative_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:50:41.003695+00:00
-- url     : https://prove2.me/theorems/1b0622f5-b017-4ea6-b9d3-b3846e974c04
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) : ‖(fockH hκ x : L2I (Occ d))‖ ^ 2 ≤ ((d : ℝ) ^ 2 / 2) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2 + (2 * d * ∑ i, κ i ^ 2)...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.fockH_relative_bound` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.fockH_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.fockH_relative_bound (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    ‖(fockH hκ x : L2I (Occ d))‖ ^ 2
      ≤ ((d : ℝ) ^ 2 / 2) * ‖(diagMax (fockSym κ) x : L2I (Occ d))‖ ^ 2
        + (2 * d * ∑ i, κ i ^ 2) * ‖(x : L2I (Occ d))‖ ^ 2 := by sorry
