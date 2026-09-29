-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_neg
-- name    : BookProof.QgHermiteFriedrichs.cpoly_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:03:46.731007+00:00
-- url     : https://prove2.me/theorems/6bcdc365-c6ca-422d-9f31-b61f2102c644
-- title:
--   The Lean 4 theorem `cpoly_neg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_neg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_neg
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_neg (p : MvPolynomial (Fin d) ℂ) : cpoly (-p) = -cpoly p := by sorry
