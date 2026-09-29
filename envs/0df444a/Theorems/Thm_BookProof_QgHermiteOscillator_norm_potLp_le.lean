-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_norm_potLp_le
-- name    : BookProof.QgHermiteOscillator.norm_potLp_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:43.701276+00:00
-- url     : https://prove2.me/theorems/850c0361-b6d7-41f9-88a9-750b156203ac
-- title:
--   The Lean 4 theorem `norm_potLp_le` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_potLp_le` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.norm_potLp_le
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

theorem BookProof.QgHermiteOscillator.norm_potLp_le {B : Vd d → ℝ} {M : ℝ} (hBc : Continuous B) (hBb : ExpBounded B)
    (hM : ∀ x, |B x| ≤ M) (p : MvPolynomial (Fin d) ℂ) :
    ‖potLp B hBc hBb p‖ ≤ M * ‖pgLp p‖ := by sorry
