-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_coe
-- name    : BookProof.NavierStokesFlow.FockCanonical.ann_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:59:12.564281+00:00
-- url     : https://prove2.me/theorems/368389b8-bfc6-4d36-bed0-a23312b150a0
-- title:
--   (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) : (((ann i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α = (Real.sqrt ((α i : ℝ) + 1) : ℂ) * ((x : L2I (Occ d)) : Occ d → ℂ) (up i α)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.ann_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.ann_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.ann_coe (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt ((α i : ℝ) + 1) : ℂ)
        * ((x : L2I (Occ d)) : Occ d → ℂ) (up i α) := by sorry
