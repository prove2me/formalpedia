-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_up
-- name    : BookProof.NavierStokesFlow.FockCanonical.dn_up
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:03:01.561409+00:00
-- url     : https://prove2.me/theorems/8f4d0d1c-14e7-42c1-83f4-50e4a001684c
-- title:
--   (i : Fin d) (α : Occ d) : dn i (up i α) = α
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.dn_up` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.dn_up
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.dn_up (i : Fin d) (α : Occ d) : dn i (up i α) = α := by sorry
