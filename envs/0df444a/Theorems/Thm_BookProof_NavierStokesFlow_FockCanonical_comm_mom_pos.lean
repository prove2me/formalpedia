-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_comm_mom_pos
-- name    : BookProof.NavierStokesFlow.FockCanonical.comm_mom_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:14:59.028151+00:00
-- url     : https://prove2.me/theorems/764e5f95-c6a2-43cd-b427-484755dfbe4e
-- title:
--   (i : Fin d) (hκ : 0 < κ i) : (mom κ i).comp (pos κ i) - (pos κ i).comp (mom κ i) = (-Complex.I) • LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.comm_mom_pos` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.comm_mom_pos
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
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

theorem BookProof.NavierStokesFlow.FockCanonical.comm_mom_pos (i : Fin d) (hκ : 0 < κ i) :
    (mom κ i).comp (pos κ i) - (pos κ i).comp (mom κ i) = (-Complex.I) • LinearMap.id := by sorry
