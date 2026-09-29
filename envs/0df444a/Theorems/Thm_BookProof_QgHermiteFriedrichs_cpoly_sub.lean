-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_sub
-- name    : BookProof.QgHermiteFriedrichs.cpoly_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:11:53.740935+00:00
-- url     : https://prove2.me/theorems/08456ed2-dbec-442f-a597-f43a054eabfb
-- title:
--   The Lean 4 theorem `cpoly_sub` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_sub` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_sub
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_sub (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p - q) = cpoly p - cpoly q := by sorry
