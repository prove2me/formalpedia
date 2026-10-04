-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_cre_coe_of_lt
-- name    : BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:14:00.757164+00:00
-- url     : https://prove2.me/theorems/42728bd0-bc92-4301-b3fa-5f1262092e02
-- title:
--   (i : Fin d) (x : lpFiniteModes (Occ d)) {β : Occ d} (h : β i < 2) : (((cre i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β = 0
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_lt` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_lt
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.Bosonic
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_lt (i : Fin d) (x : lpFiniteModes (Occ d)) {β : Occ d}
    (h : β i < 2) :
    (((cre i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β = 0 := by sorry
