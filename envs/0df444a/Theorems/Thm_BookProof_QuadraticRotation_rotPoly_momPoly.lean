-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotPoly_momPoly
-- name    : BookProof.QuadraticRotation.rotPoly_momPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:02:01.041215+00:00
-- url     : https://prove2.me/theorems/618ffa5c-9861-42ec-ab66-5ab8c5c1f7d2
-- title:
--   The Lean 4 theorem `rotPoly_momPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.rotPoly_momPoly` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotPoly_momPoly
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

theorem BookProof.QuadraticRotation.rotPoly_momPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (momPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • momPoly k (rotPoly O p) := by sorry
