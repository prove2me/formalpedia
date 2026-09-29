-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_anti_DS
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.anti_DS
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:30:09.276627+00:00
-- url     : https://prove2.me/theorems/44a5f16e-94c0-49a6-b4cc-7650a08deea9
-- title:
--   : (cre - ann).comp (cre + ann) + (cre + ann).comp (cre - ann) = (2 : ℂ) • (cre.comp cre - ann.comp ann)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.anti_DS` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.anti_DS
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.anti_DS :
    (cre - ann).comp (cre + ann) + (cre + ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp cre - ann.comp ann) := by sorry
