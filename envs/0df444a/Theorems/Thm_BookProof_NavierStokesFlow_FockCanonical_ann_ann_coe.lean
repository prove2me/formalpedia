-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_ann_coe
-- name    : BookProof.NavierStokesFlow.FockCanonical.ann_ann_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:50:04.485232+00:00
-- url     : https://prove2.me/theorems/30f584cd-29a7-420d-ba8a-1ca136522046
-- title:
--   (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) : (((ann i (ann i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α = (Real.sqrt ((α i : ℝ) + 1) : ℂ) * (Real.sqrt ((α i...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.ann_ann_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.ann_ann_coe
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

theorem BookProof.NavierStokesFlow.FockCanonical.ann_ann_coe (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i (ann i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt ((α i : ℝ) + 1) : ℂ) * (Real.sqrt ((α i : ℝ) + 2) : ℂ)
        * ((x : L2I (Occ d)) : Occ d → ℂ) (modeShift i α) := by sorry
