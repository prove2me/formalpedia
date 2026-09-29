-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_kinPoly_add_harmPoly_hermiteMv
-- name    : BookProof.QgHermiteOscillator.kinPoly_add_harmPoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:27:20.218909+00:00
-- url     : https://prove2.me/theorems/29665c22-9824-4f5e-af51-5e1f42b04787
-- title:
--   The Lean 4 theorem `kinPoly_add_harmPoly_hermiteMv` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `kinPoly_add_harmPoly_hermiteMv` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.kinPoly_add_harmPoly_hermiteMv
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

theorem BookProof.QgHermiteOscillator.kinPoly_add_harmPoly_hermiteMv (a : Fin d →₀ ℕ) :
    kinPoly (hermiteMv a) + harmPoly * hermiteMv a
      = (((mvDeg a : ℂ) + (d : ℂ) / 2)) • hermiteMv a := by sorry
