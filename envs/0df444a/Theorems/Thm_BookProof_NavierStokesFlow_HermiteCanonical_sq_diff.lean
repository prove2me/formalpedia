-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_sq_diff
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.sq_diff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:55:53.705702+00:00
-- url     : https://prove2.me/theorems/0b77daab-4382-45af-984a-544d8686fe8d
-- title:
--   : (cre + ann).comp (cre + ann) - (cre - ann).comp (cre - ann) = (2 : ℂ) • (cre.comp ann + ann.comp cre)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.sq_diff` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.sq_diff
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.sq_diff :
    (cre + ann).comp (cre + ann) - (cre - ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp ann + ann.comp cre) := by sorry
