-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_eq_zero_of_inner_basis_eq_zero
-- name    : BookProof.QgHermiteOscillator.eq_zero_of_inner_basis_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:51.213485+00:00
-- url     : https://prove2.me/theorems/ace06926-58f3-4d8f-a280-bce6f255f402
-- title:
--   The Lean 4 theorem `eq_zero_of_inner_basis_eq_zero` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eq_zero_of_inner_basis_eq_zero` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.eq_zero_of_inner_basis_eq_zero
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

theorem BookProof.QgHermiteOscillator.eq_zero_of_inner_basis_eq_zero (b : HilbertBasis ι ℂ F) {w : F}
    (h : ∀ i, (inner ℂ (b i) w : ℂ) = 0) : w = 0 := by sorry
