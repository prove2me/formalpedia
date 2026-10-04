-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_hop_modeData_eq
-- name    : BookProof.NavierStokesFlow.FockCanonical.hop_modeData_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:16:41.425861+00:00
-- url     : https://prove2.me/theorems/c1c4dcd7-7368-4455-b7d1-21d77f14aca7
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (g : Occ d → ℂ) (β : Occ d) : (modeData hκ i).hop g β = if 2 ≤ β i then g (dn i (dn i β)) else 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.hop_modeData_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.hop_modeData_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.hop_modeData_eq (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (g : Occ d → ℂ) (β : Occ d) :
    (modeData hκ i).hop g β = if 2 ≤ β i then g (dn i (dn i β)) else 0 := by sorry
