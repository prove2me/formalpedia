-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmCore_hermiteMvLp
-- name    : BookProof.QgHermiteOscillator.harmCore_hermiteMvLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:53:48.957556+00:00
-- url     : https://prove2.me/theorems/abd22123-6dbc-406e-b900-2451cfb2dd33
-- title:
--   The Lean 4 theorem `harmCore_hermiteMvLp` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmCore_hermiteMvLp` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmCore_hermiteMvLp
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

theorem BookProof.QgHermiteOscillator.harmCore_hermiteMvLp (a : Fin d →₀ ℕ) :
    harmCore ⟨hermiteMvLp a, hermiteMvLp_mem_core a⟩
      = (((mvDeg a : ℝ) + (d : ℝ) / 2 : ℝ) : ℂ) • (hermiteMvLp a : L2d d) := by sorry
