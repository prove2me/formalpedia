-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_momPoly_apply_prime
-- name    : BookProof.HyperbolicQuadratic.momPoly_apply_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T07:23:11.932279+00:00
-- url     : https://prove2.me/theorems/8fa7db46-0e86-4a81-a781-a60706c5674f
-- title:
--   The Lean 4 theorem `momPoly_apply_prime` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momPoly_apply'` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.momPoly_apply'
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
variable {d : ℕ}



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

theorem BookProof.HyperbolicQuadratic.momPoly_apply_prime (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = (-Complex.I) • (pderiv i p - (1/2 : ℂ) • (X i * p)) := by sorry
