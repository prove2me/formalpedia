-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_momPoly_sq
-- name    : BookProof.HyperbolicQuadratic.momPoly_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:02:18.384998+00:00
-- url     : https://prove2.me/theorems/ed5c4468-a2aa-4fa8-b68c-3068a7206c40
-- title:
--   The Lean 4 theorem `momPoly_sq` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momPoly_sq` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.momPoly_sq
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.momPoly_sq (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (momPoly i p)
      = -(pderiv i (pderiv i p)) + (1/2 : ℂ) • p + X i * pderiv i p
        - (1/4 : ℂ) • (X i * (X i * p)) := by sorry
