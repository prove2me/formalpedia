-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmonicCore_quadForm_nonneg
-- name    : BookProof.QgHermiteOscillator.harmonicCore_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:33.90976+00:00
-- url     : https://prove2.me/theorems/4f9f0d27-afd5-4e76-922b-565128c63f49
-- title:
--   The Lean 4 theorem `harmonicCore_quadForm_nonneg` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonicCore_quadForm_nonneg` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmonicCore_quadForm_nonneg
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

theorem BookProof.QgHermiteOscillator.harmonicCore_quadForm_nonneg (x : polyGaussCore (d := d)) : 0 ≤ quadForm harmCore x := by sorry
