-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_kinPoly_left
-- name    : BookProof.QgHermiteFriedrichs.gaussInt_kinPoly_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:04.453149+00:00
-- url     : https://prove2.me/theorems/8f067308-db44-4b76-b1f3-7cf092e694f4
-- title:
--   The Lean 4 theorem `gaussInt_kinPoly_left` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_kinPoly_left` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.gaussInt_kinPoly_left
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.gaussInt_kinPoly_left (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by sorry
