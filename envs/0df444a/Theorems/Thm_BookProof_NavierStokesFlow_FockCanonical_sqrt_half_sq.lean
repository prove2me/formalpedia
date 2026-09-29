-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_sqrt_half_sq
-- name    : BookProof.NavierStokesFlow.FockCanonical.sqrt_half_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:05:01.475754+00:00
-- url     : https://prove2.me/theorems/4239c609-dd62-49e4-9f54-3aee5d0b201d
-- title:
--   (i : Fin d) (hκ : 0 ≤ κ i) : (Real.sqrt (κ i / 2) : ℂ) * (Real.sqrt (κ i / 2) : ℂ) = (κ i : ℂ) / 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.sqrt_half_sq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.sqrt_half_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.sqrt_half_sq (i : Fin d) (hκ : 0 ≤ κ i) :
    (Real.sqrt (κ i / 2) : ℂ) * (Real.sqrt (κ i / 2) : ℂ) = (κ i : ℂ) / 2 := by sorry
