-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_coreD_raw
-- name    : BookProof.QgHermiteFriedrichs.gaussInt_coreD_raw
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:12.929441+00:00
-- url     : https://prove2.me/theorems/6829d447-e849-49a3-9815-9a3141ed5e31
-- title:
--   The Lean 4 theorem `gaussInt_coreD_raw` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_coreD_raw` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.gaussInt_coreD_raw
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.gaussInt_coreD_raw (j : Fin d) (a b : MvPolynomial (Fin d) ℂ) :
    gaussInt (coreD j a * b) = -gaussInt (a * coreD j b) := by sorry
