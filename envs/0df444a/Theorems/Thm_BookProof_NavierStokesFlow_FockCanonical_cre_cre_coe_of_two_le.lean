-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_cre_coe_of_two_le
-- name    : BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_two_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:30:04.645496+00:00
-- url     : https://prove2.me/theorems/39afdc96-a599-44d2-a2ae-860ffce4c187
-- title:
--   (i : Fin d) (x : lpFiniteModes (Occ d)) {β : Occ d} (h : 2 ≤ β i) : (((cre i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β = (Real.sqrt (β i : ℝ) : ℂ) *...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_two_le` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_two_le
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

theorem BookProof.NavierStokesFlow.FockCanonical.cre_cre_coe_of_two_le (i : Fin d) (x : lpFiniteModes (Occ d)) {β : Occ d}
    (h : 2 ≤ β i) :
    (((cre i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β
      = (Real.sqrt (β i : ℝ) : ℂ) * (Real.sqrt ((β i : ℝ) - 1) : ℂ)
        * ((x : L2I (Occ d)) : Occ d → ℂ) (dn i (dn i β)) := by sorry
