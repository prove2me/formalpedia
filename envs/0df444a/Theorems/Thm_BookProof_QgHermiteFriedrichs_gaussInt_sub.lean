-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_sub
-- name    : BookProof.QgHermiteFriedrichs.gaussInt_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:43.148764+00:00
-- url     : https://prove2.me/theorems/91fe1f87-581a-4019-9430-f07bacf117d7
-- title:
--   The Lean 4 theorem `gaussInt_sub` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_sub` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.gaussInt_sub
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by sorry
