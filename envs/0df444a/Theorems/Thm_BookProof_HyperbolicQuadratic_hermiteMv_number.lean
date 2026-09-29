-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_hermiteMv_number
-- name    : BookProof.HyperbolicQuadratic.hermiteMv_number
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:11.497897+00:00
-- url     : https://prove2.me/theorems/f14c6d18-f62b-4244-a183-9b8e939b1cb4
-- title:
--   The Lean 4 theorem `hermiteMv_number` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteMv_number` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.hermiteMv_number
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.hermiteMv_number (i : Fin d) (a : Fin d →₀ ℕ) :
    X i * pderiv i (hermiteMv a) - pderiv i (pderiv i (hermiteMv a))
      = ((a i : ℂ)) • hermiteMv a := by sorry
