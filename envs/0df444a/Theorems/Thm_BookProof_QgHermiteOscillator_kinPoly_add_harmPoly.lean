-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_kinPoly_add_harmPoly
-- name    : BookProof.QgHermiteOscillator.kinPoly_add_harmPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:39.296292+00:00
-- url     : https://prove2.me/theorems/c112d74e-5539-458c-836e-61593a916b2d
-- title:
--   The Lean 4 theorem `kinPoly_add_harmPoly` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `kinPoly_add_harmPoly` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.kinPoly_add_harmPoly
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

theorem BookProof.QgHermiteOscillator.kinPoly_add_harmPoly (p : MvPolynomial (Fin d) ℂ) :
    kinPoly p + harmPoly * p
      = (∑ j : Fin d, crePoly j (annPoly j p)) + C ((d : ℂ) / 2) * p := by sorry
