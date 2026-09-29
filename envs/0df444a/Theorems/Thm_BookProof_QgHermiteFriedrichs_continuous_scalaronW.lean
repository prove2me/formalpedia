-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_continuous_scalaronW
-- name    : BookProof.QgHermiteFriedrichs.continuous_scalaronW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:02:11.589881+00:00
-- url     : https://prove2.me/theorems/9197a21a-0143-43cc-976f-82f9d82c495a
-- title:
--   The Lean 4 theorem `continuous_scalaronW` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `continuous_scalaronW` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.continuous_scalaronW
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.continuous_scalaronW (M alpha : ℝ) : Continuous (scalaronW M alpha) := by sorry
