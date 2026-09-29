-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_anti_DS
-- name    : BookProof.NavierStokesFlow.FockCanonical.anti_DS
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T15:00:20.106173+00:00
-- url     : https://prove2.me/theorems/d8ac7df6-1c49-4e33-88af-be66cb6420f6
-- title:
--   (i : Fin d) : (cre i - ann i).comp (cre i + ann i) + (cre i + ann i).comp (cre i - ann i) = (2 : ℂ) • ((cre i).comp (cre i) - (ann i).comp (ann i))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.anti_DS` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.anti_DS
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.anti_DS (i : Fin d) :
    (cre i - ann i).comp (cre i + ann i) + (cre i + ann i).comp (cre i - ann i)
      = (2 : ℂ) • ((cre i).comp (cre i) - (ann i).comp (ann i)) := by sorry
