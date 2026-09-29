-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_scalaronW_nonneg
-- name    : BookProof.QgHermiteFriedrichs.scalaronW_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:52.180569+00:00
-- url     : https://prove2.me/theorems/1104f12a-bc69-49b8-9ba2-661f8186f71c
-- title:
--   The Lean 4 theorem `scalaronW_nonneg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `scalaronW_nonneg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.scalaronW_nonneg
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

theorem BookProof.QgHermiteFriedrichs.scalaronW_nonneg {M alpha : ℝ} (halpha : 0 < alpha) (x : Vd 1) :
    0 ≤ scalaronW M alpha x := by sorry
