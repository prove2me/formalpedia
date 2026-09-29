-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_coe
-- name    : BookProof.NavierStokesFlow.FockCanonical.cre_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:01:09.696947+00:00
-- url     : https://prove2.me/theorems/baf85766-bb30-46a4-ad73-34ee051f34df
-- title:
--   (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) : (((cre i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α = (Real.sqrt (α i : ℝ) : ℂ) * ((x : L2I (Occ d)) : Occ d → ℂ) (dn i α)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.cre_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.cre_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.cre_coe (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((cre i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (Real.sqrt (α i : ℝ) : ℂ) * ((x : L2I (Occ d)) : Occ d → ℂ) (dn i α) := by sorry
