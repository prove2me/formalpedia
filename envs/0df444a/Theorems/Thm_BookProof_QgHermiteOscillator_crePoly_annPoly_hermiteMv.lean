-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_crePoly_annPoly_hermiteMv
-- name    : BookProof.QgHermiteOscillator.crePoly_annPoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:59.069983+00:00
-- url     : https://prove2.me/theorems/aee9127b-38af-49af-9687-f6528156b9bb
-- title:
--   The Lean 4 theorem `crePoly_annPoly_hermiteMv` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `crePoly_annPoly_hermiteMv` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.crePoly_annPoly_hermiteMv
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

theorem BookProof.QgHermiteOscillator.crePoly_annPoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (annPoly i (hermiteMv a)) = ((a i : ℂ)) • hermiteMv a := by sorry
