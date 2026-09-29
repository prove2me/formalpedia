-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_modeData_sym
-- name    : BookProof.NavierStokesFlow.FockManyMode.modeData_sym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:08:24.95715+00:00
-- url     : https://prove2.me/theorems/894f4544-b280-4367-b2fa-f437efe3a66b
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) : (modeData hκ i).sym = fockSym κ
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.modeData_sym` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.modeData_sym
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockManyMode.modeData_sym (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) :
    (modeData hκ i).sym = fockSym κ := by sorry
