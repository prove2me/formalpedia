-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_modeShift_dn_dn
-- name    : BookProof.NavierStokesFlow.FockCanonical.modeShift_dn_dn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:50:20.627201+00:00
-- url     : https://prove2.me/theorems/def0b862-18af-4a81-9819-3561f4514d5e
-- title:
--   (i : Fin d) {β : Occ d} (h : 2 ≤ β i) : modeShift i (dn i (dn i β)) = β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.modeShift_dn_dn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.modeShift_dn_dn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.modeShift_dn_dn (i : Fin d) {β : Occ d} (h : 2 ≤ β i) :
    modeShift i (dn i (dn i β)) = β := by sorry
