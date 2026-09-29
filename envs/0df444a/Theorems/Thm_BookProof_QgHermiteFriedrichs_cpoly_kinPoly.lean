-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_kinPoly
-- name    : BookProof.QgHermiteFriedrichs.cpoly_kinPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:21:25.634002+00:00
-- url     : https://prove2.me/theorems/89f9e33b-c054-4404-a427-7314ca215c98
-- title:
--   The Lean 4 theorem `cpoly_kinPoly` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_kinPoly` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_kinPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_kinPoly (p : MvPolynomial (Fin d) ℂ) :
    cpoly (kinPoly p) = kinPoly (cpoly p) := by sorry
