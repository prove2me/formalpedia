-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmonicCore_dense
-- name    : BookProof.QgHermiteOscillator.harmonicCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:24.951135+00:00
-- url     : https://prove2.me/theorems/654ca418-eb69-4492-8d8d-52197f1eacfe
-- title:
--   The Lean 4 theorem `harmonicCore_dense` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonicCore_dense` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmonicCore_dense
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

theorem BookProof.QgHermiteOscillator.harmonicCore_dense : Dense ((polyGaussCore (d := d) : Submodule ℂ (L2d d)) : Set (L2d d)) := by sorry
