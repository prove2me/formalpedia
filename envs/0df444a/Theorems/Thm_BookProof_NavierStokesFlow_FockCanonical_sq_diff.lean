-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_sq_diff
-- name    : BookProof.NavierStokesFlow.FockCanonical.sq_diff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:03:41.874728+00:00
-- url     : https://prove2.me/theorems/5491fe3f-716c-444c-9365-fc4c87689041
-- title:
--   (i : Fin d) : (cre i + ann i).comp (cre i + ann i) - (cre i - ann i).comp (cre i - ann i) = (2 : ℂ) • ((cre i).comp (ann i) + (ann i).comp (cre i))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.sq_diff` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.sq_diff
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.sq_diff (i : Fin d) :
    (cre i + ann i).comp (cre i + ann i) - (cre i - ann i).comp (cre i - ann i)
      = (2 : ℂ) • ((cre i).comp (ann i) + (ann i).comp (cre i)) := by sorry
