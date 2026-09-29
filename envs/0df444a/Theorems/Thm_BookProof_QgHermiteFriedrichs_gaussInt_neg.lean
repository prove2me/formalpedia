-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_neg
-- name    : BookProof.QgHermiteFriedrichs.gaussInt_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:30.195253+00:00
-- url     : https://prove2.me/theorems/592ef3b8-4101-4801-bfa2-99fad55a2f6d
-- title:
--   The Lean 4 theorem `gaussInt_neg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_neg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.gaussInt_neg
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.gaussInt_neg (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by sorry
