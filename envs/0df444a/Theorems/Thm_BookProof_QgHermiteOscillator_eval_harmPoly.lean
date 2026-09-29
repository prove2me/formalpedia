-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_eval_harmPoly
-- name    : BookProof.QgHermiteOscillator.eval_harmPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:14.030071+00:00
-- url     : https://prove2.me/theorems/e5ed5aa2-5a82-4204-8709-311511ace983
-- title:
--   The Lean 4 theorem `eval_harmPoly` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eval_harmPoly` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.eval_harmPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.QgHermiteOscillator











open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}





variable {d : ℕ}

theorem BookProof.QgHermiteOscillator.eval_harmPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (harmPoly (d := d)) = ((harmW x : ℝ) : ℂ) := by sorry
