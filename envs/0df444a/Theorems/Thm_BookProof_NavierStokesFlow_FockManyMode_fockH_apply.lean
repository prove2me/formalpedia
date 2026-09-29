-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_apply
-- name    : BookProof.NavierStokesFlow.FockManyMode.fockH_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:07:12.679158+00:00
-- url     : https://prove2.me/theorems/ddfd4425-e8f5-4247-a9ca-a31ac886d9ae
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) : (fockH hκ x : L2I (Occ d)) = ∑ i, (ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.fockH_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.fockH_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockManyMode.fockH_apply (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    (fockH hκ x : L2I (Occ d)) = ∑ i, (ShiftData.shiftH (modeData hκ i) x : L2I (Occ d)) := by sorry
