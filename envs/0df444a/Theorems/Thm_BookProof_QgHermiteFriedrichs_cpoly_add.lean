-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_add
-- name    : BookProof.QgHermiteFriedrichs.cpoly_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:04:02.265159+00:00
-- url     : https://prove2.me/theorems/a624b3ee-515c-4a8d-a138-70b628ac87bf
-- title:
--   The Lean 4 theorem `cpoly_add` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_add` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_add
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_add (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p + q) = cpoly p + cpoly q := by sorry
