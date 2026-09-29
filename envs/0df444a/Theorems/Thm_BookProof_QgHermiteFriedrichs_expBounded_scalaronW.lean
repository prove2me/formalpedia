-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_expBounded_scalaronW
-- name    : BookProof.QgHermiteFriedrichs.expBounded_scalaronW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:19.85805+00:00
-- url     : https://prove2.me/theorems/20935972-7a96-46af-ab65-e2c733262d8f
-- title:
--   The Lean 4 theorem `expBounded_scalaronW` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `expBounded_scalaronW` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.expBounded_scalaronW
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

theorem BookProof.QgHermiteFriedrichs.expBounded_scalaronW (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronW M alpha) := by sorry
