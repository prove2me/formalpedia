-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_coordLine_apply
-- name    : BookProof.QgHermiteFriedrichs.coordLine_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:02:29.303985+00:00
-- url     : https://prove2.me/theorems/fb4ae9df-e5fb-4a87-ab1f-4a6d47e7eb35
-- title:
--   The Lean 4 theorem `coordLine_apply` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coordLine_apply` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.coordLine_apply
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

theorem BookProof.QgHermiteFriedrichs.coordLine_apply (x : Vd d) (j : Fin d) (s : ℝ) (i : Fin d) :
    (coordLine x j s) i = Function.update x.ofLp j s i := by sorry
