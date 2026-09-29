-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_coreEquiv_apply
-- name    : BookProof.QgHermiteFriedrichs.coreEquiv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:02:21.594424+00:00
-- url     : https://prove2.me/theorems/e771f728-240f-4dcc-a9c3-819028175d3e
-- title:
--   The Lean 4 theorem `coreEquiv_apply` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreEquiv_apply` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.coreEquiv_apply
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

theorem BookProof.QgHermiteFriedrichs.coreEquiv_apply (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := by sorry
