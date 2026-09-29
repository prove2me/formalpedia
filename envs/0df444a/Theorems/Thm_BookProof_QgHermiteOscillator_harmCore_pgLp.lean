-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_harmCore_pgLp
-- name    : BookProof.QgHermiteOscillator.harmCore_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:27:19.621737+00:00
-- url     : https://prove2.me/theorems/c7e340e8-1298-4477-96c5-0fc812826fa0
-- title:
--   The Lean 4 theorem `harmCore_pgLp` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmCore_pgLp` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.harmCore_pgLp
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

theorem BookProof.QgHermiteOscillator.harmCore_pgLp (p : MvPolynomial (Fin d) ℂ) :
    harmCore ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (kinPoly p + harmPoly * p) := by sorry
