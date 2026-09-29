-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_potLp_harmW
-- name    : BookProof.QgHermiteOscillator.potLp_harmW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:49.266206+00:00
-- url     : https://prove2.me/theorems/0a650a33-20a8-4a07-848a-d9332aba03a0
-- title:
--   The Lean 4 theorem `potLp_harmW` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `potLp_harmW` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.potLp_harmW
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

theorem BookProof.QgHermiteOscillator.potLp_harmW (p : MvPolynomial (Fin d) ℂ) :
    potLp harmW continuous_harmW expBounded_harmW p = pgLp (harmPoly * p) := by sorry
