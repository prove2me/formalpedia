-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_dn_self
-- name    : BookProof.NavierStokesFlow.FockCanonical.dn_dn_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:31:35.958198+00:00
-- url     : https://prove2.me/theorems/b09da576-288d-43e4-80ba-4c4ebcaf8cd6
-- title:
--   (i : Fin d) (β : Occ d) : (dn i (dn i β)) i = β i - 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.dn_dn_self` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.dn_dn_self
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

theorem BookProof.NavierStokesFlow.FockCanonical.dn_dn_self (i : Fin d) (β : Occ d) : (dn i (dn i β)) i = β i - 2 := by sorry
