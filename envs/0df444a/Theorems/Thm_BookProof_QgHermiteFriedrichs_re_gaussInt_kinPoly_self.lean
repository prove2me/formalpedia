-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_re_gaussInt_kinPoly_self
-- name    : BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:00.937444+00:00
-- url     : https://prove2.me/theorems/c1f28602-f01f-484c-86cc-7adf4b2d54ea
-- title:
--   The Lean 4 theorem `re_gaussInt_kinPoly_self` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `re_gaussInt_kinPoly_self` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self
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































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self (p : MvPolynomial (Fin d) ℂ) :
    (gaussInt (cpoly p * kinPoly p)).re = ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 := by sorry
