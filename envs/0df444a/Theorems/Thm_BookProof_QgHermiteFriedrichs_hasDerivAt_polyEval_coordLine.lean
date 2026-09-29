-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_polyEval_coordLine
-- name    : BookProof.QgHermiteFriedrichs.hasDerivAt_polyEval_coordLine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:20:59.483556+00:00
-- url     : https://prove2.me/theorems/962545f8-0edb-4783-b2f4-b1aa64d5c8f5
-- title:
--   The Lean 4 theorem `hasDerivAt_polyEval_coordLine` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_polyEval_coordLine` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hasDerivAt_polyEval_coordLine
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

theorem BookProof.QgHermiteFriedrichs.hasDerivAt_polyEval_coordLine (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (j : Fin d)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun i => (((coordLine x j s) i : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun i => (((coordLine x j t) i : ℝ) : ℂ)) (pderiv j p)) t := by sorry
