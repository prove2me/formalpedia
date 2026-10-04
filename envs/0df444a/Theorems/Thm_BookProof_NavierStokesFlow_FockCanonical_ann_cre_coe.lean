-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_cre_coe
-- name    : BookProof.NavierStokesFlow.FockCanonical.ann_cre_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:49:57.692545+00:00
-- url     : https://prove2.me/theorems/08c12bad-1b0b-432c-a9ae-5ca2e9c6299c
-- title:
--   (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) : (((ann i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α = ((α i : ℂ) + 1) * ((x : L2I (Occ d)) : Occ d → ℂ) α
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.ann_cre_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.ann_cre_coe
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

theorem BookProof.NavierStokesFlow.FockCanonical.ann_cre_coe (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i (cre i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = ((α i : ℂ) + 1) * ((x : L2I (Occ d)) : Occ d → ℂ) α := by sorry
