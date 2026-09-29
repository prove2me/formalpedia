-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_kinPoly
-- name    : BookProof.QgHermiteFriedrichs.gaussInt_kinPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:12.27264+00:00
-- url     : https://prove2.me/theorems/55efde7d-d37f-45b5-bfd5-ca1ba7d2e04f
-- title:
--   The Lean 4 theorem `gaussInt_kinPoly` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_kinPoly` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.gaussInt_kinPoly
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

theorem BookProof.QgHermiteFriedrichs.gaussInt_kinPoly (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly p * kinPoly q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by sorry
