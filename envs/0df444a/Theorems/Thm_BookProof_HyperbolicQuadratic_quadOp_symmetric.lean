-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_symmetric
-- name    : BookProof.HyperbolicQuadratic.quadOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:49.220585+00:00
-- url     : https://prove2.me/theorems/1b706eee-3f73-47d7-b556-78ce921cabd4
-- title:
--   The Lean 4 theorem `quadOp_symmetric` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_symmetric` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadOp_symmetric
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadOp_symmetric (c : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (quadOp c) := by sorry
