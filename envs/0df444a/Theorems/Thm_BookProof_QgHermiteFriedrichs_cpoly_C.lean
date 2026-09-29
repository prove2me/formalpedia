-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_C
-- name    : BookProof.QgHermiteFriedrichs.cpoly_C
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:03:47.97399+00:00
-- url     : https://prove2.me/theorems/033d2b24-ae36-4291-9494-a4c664f23537
-- title:
--   The Lean 4 theorem `cpoly_C` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_C` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_C
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_C (a : ℂ) :
    cpoly (C a : MvPolynomial (Fin d) ℂ) = C (starRingEnd ℂ a) := by sorry
