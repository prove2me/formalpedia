-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_expBounded_of_bounded
-- name    : BookProof.QgHermiteOscillator.expBounded_of_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:23.26522+00:00
-- url     : https://prove2.me/theorems/ab45871f-2c41-4247-ab4f-e426c813a1c0
-- title:
--   The Lean 4 theorem `expBounded_of_bounded` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `expBounded_of_bounded` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.expBounded_of_bounded
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

theorem BookProof.QgHermiteOscillator.expBounded_of_bounded {B : Vd d → ℝ} {M : ℝ} (hM : ∀ x, |B x| ≤ M) : ExpBounded B := by sorry
