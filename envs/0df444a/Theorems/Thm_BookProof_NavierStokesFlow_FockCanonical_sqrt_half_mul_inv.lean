-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_sqrt_half_mul_inv
-- name    : BookProof.NavierStokesFlow.FockCanonical.sqrt_half_mul_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:04:22.433768+00:00
-- url     : https://prove2.me/theorems/a5dc8b8e-f74a-49f2-a51d-92f993a7a205
-- title:
--   (i : Fin d) (hκ : 0 < κ i) : (Real.sqrt (κ i / 2) : ℂ) * ((1 / Real.sqrt (2 * κ i) : ℝ) : ℂ) = 1 / 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.sqrt_half_mul_inv` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.sqrt_half_mul_inv
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.sqrt_half_mul_inv (i : Fin d) (hκ : 0 < κ i) :
    (Real.sqrt (κ i / 2) : ℂ) * ((1 / Real.sqrt (2 * κ i) : ℝ) : ℂ) = 1 / 2 := by sorry
