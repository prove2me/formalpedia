-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_symmetricOn
-- name    : BookProof.NavierStokesFlow.FockManyMode.fockH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:50:56.487287+00:00
-- url     : https://prove2.me/theorems/8abc3581-b1fc-4e11-93b1-9a6209036add
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) : SymmetricOn (maxDom (fockSym κ)) (fockH hκ)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.fockH_symmetricOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.fockH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.NavierStokesFlow.FockManyMode.fockH_symmetricOn (hκ : ∀ i, 0 ≤ κ i) :
    SymmetricOn (maxDom (fockSym κ)) (fockH hκ) := by sorry
