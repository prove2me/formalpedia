-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
-- name    : BookProof.HyperbolicQuadratic.quadPoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:13.575432+00:00
-- url     : https://prove2.me/theorems/a9804df9-85d3-48e7-a18f-d626b6200e02
-- title:
--   The Lean 4 theorem `quadPoly_hermiteMv` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadPoly_hermiteMv` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadPoly_hermiteMv
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadPoly_hermiteMv (c : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    quadPoly c (hermiteMv a) = ((quadSymbol c a : ℝ) : ℂ) • hermiteMv a := by sorry
