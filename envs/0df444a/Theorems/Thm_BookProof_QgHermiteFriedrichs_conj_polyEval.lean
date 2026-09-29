-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_polyEval
-- name    : BookProof.QgHermiteFriedrichs.conj_polyEval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:12:48.395162+00:00
-- url     : https://prove2.me/theorems/c5e5816e-efa0-4037-a597-705089548edb
-- title:
--   The Lean 4 theorem `conj_polyEval` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `conj_polyEval` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.conj_polyEval
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.conj_polyEval (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p) := by sorry
