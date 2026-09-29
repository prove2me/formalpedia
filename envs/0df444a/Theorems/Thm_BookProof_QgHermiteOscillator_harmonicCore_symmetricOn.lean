-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmonicCore_symmetricOn
-- name    : BookProof.QgHermiteOscillator.harmonicCore_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:32.107078+00:00
-- url     : https://prove2.me/theorems/891a94e7-0b42-4249-ae5e-ebec1b1c5017
-- title:
--   The Lean 4 theorem `harmonicCore_symmetricOn` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonicCore_symmetricOn` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmonicCore_symmetricOn
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

theorem BookProof.QgHermiteOscillator.harmonicCore_symmetricOn : SymmetricOn (polyGaussCore (d := d)) harmCore := by sorry
