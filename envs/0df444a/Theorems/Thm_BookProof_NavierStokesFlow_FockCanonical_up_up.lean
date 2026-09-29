-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_up_up
-- name    : BookProof.NavierStokesFlow.FockCanonical.up_up
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:06:25.923904+00:00
-- url     : https://prove2.me/theorems/3c7b8dc7-229c-43ba-98e5-6226a1188191
-- title:
--   (i : Fin d) (α : Occ d) : up i (up i α) = modeShift i α
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.up_up` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.up_up
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.up_up (i : Fin d) (α : Occ d) : up i (up i α) = modeShift i α := by sorry
