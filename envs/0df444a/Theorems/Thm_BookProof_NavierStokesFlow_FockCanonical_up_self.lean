-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_up_self
-- name    : BookProof.NavierStokesFlow.FockCanonical.up_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:05:37.834887+00:00
-- url     : https://prove2.me/theorems/ec7e9bbb-42a7-4750-9917-7b6e07bb0e38
-- title:
--   (i : Fin d) (α : Occ d) : up i α i = α i + 1
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.up_self` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.up_self
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.up_self (i : Fin d) (α : Occ d) : up i α i = α i + 1 := by sorry
