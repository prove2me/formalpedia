-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_mode_comparison_eq
-- name    : BookProof.NavierStokesFlow.FockCanonical.mode_comparison_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:49:36.292847+00:00
-- url     : https://prove2.me/theorems/74a569e5-ffb7-4186-a19b-3adb802bfe34
-- title:
--   (i : Fin d) (hκ : 0 ≤ κ i) : (mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i) = (κ i : ℂ) • ((cre i).comp (ann i) + (ann i).comp (cre i))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.mode_comparison_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.mode_comparison_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.Bosonic
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.mode_comparison_eq (i : Fin d) (hκ : 0 ≤ κ i) :
    (mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i)
      = (κ i : ℂ) • ((cre i).comp (ann i) + (ann i).comp (cre i)) := by sorry
