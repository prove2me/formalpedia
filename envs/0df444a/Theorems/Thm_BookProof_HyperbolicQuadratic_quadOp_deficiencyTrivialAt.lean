-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_deficiencyTrivialAt
-- name    : BookProof.HyperbolicQuadratic.quadOp_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:42.648976+00:00
-- url     : https://prove2.me/theorems/48830fdb-c650-4b2b-8633-c1ffb7fcd2a0
-- title:
--   The Lean 4 theorem `quadOp_deficiencyTrivialAt` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_deficiencyTrivialAt` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadOp_deficiencyTrivialAt (c : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (quadOp c) z := by sorry
