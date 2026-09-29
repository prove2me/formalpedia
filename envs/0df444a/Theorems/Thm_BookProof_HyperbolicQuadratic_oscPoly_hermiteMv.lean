-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_oscPoly_hermiteMv
-- name    : BookProof.HyperbolicQuadratic.oscPoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:05:49.92533+00:00
-- url     : https://prove2.me/theorems/92c71353-7642-47dd-bbad-8b89d5897e16
-- title:
--   The Lean 4 theorem `oscPoly_hermiteMv` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `oscPoly_hermiteMv` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.oscPoly_hermiteMv
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.oscPoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    oscPoly i (hermiteMv a) = (((a i : ℝ) : ℂ) + 1/2) • hermiteMv a := by sorry
