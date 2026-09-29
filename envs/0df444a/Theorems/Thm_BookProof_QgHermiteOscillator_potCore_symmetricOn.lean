-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_potCore_symmetricOn
-- name    : BookProof.QgHermiteOscillator.potCore_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:15.730856+00:00
-- url     : https://prove2.me/theorems/5592d6c8-4d0c-45a2-8428-86f6c86bdc8f
-- title:
--   The Lean 4 theorem `potCore_symmetricOn` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `potCore_symmetricOn` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.potCore_symmetricOn
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

theorem BookProof.QgHermiteOscillator.potCore_symmetricOn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (potCore W hWc hWb) := by sorry
