-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotPoly_mulXPoly
-- name    : BookProof.QuadraticRotation.rotPoly_mulXPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:02:09.423416+00:00
-- url     : https://prove2.me/theorems/5bcb5499-29b4-4ce2-b0ec-19efae6eb224
-- title:
--   The Lean 4 theorem `rotPoly_mulXPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.rotPoly_mulXPoly` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotPoly_mulXPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.rotPoly_mulXPoly (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (mulXPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • mulXPoly k (rotPoly O p) := by sorry
