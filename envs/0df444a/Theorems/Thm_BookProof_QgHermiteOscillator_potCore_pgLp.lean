-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_potCore_pgLp
-- name    : BookProof.QgHermiteOscillator.potCore_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:13:33.055526+00:00
-- url     : https://prove2.me/theorems/bee6af04-f091-478e-be98-c3c326b01319
-- title:
--   The Lean 4 theorem `potCore_pgLp` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `potCore_pgLp` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.potCore_pgLp
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

theorem BookProof.QgHermiteOscillator.potCore_pgLp (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    potCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = potLp W hWc hWb p := by sorry
