-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_coreD_sq_add_harm
-- name    : BookProof.QgHermiteOscillator.coreD_sq_add_harm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:02.766878+00:00
-- url     : https://prove2.me/theorems/b2caf4b3-4f85-4fe3-be33-2d71a0a07471
-- title:
--   The Lean 4 theorem `coreD_sq_add_harm` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreD_sq_add_harm` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.coreD_sq_add_harm
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

theorem BookProof.QgHermiteOscillator.coreD_sq_add_harm (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    -coreD j (coreD j p) + C (1 / 4 : ℂ) * (X j ^ 2 * p)
      = crePoly j (annPoly j p) + C (1 / 2 : ℂ) * p := by sorry
