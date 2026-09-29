-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_pderiv
-- name    : BookProof.QgHermiteFriedrichs.cpoly_pderiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:11:45.037668+00:00
-- url     : https://prove2.me/theorems/880f216d-dce1-4bc4-a746-de3bb38c7ff2
-- title:
--   The Lean 4 theorem `cpoly_pderiv` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_pderiv` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_pderiv
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (pderiv j p) = pderiv j (cpoly p) := by sorry
