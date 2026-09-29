-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_hermiteMvLp
-- name    : BookProof.HyperbolicQuadratic.quadOp_hermiteMvLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:40.739113+00:00
-- url     : https://prove2.me/theorems/ce6670bb-f5e8-45d5-8c96-ddcb69979cab
-- title:
--   The Lean 4 theorem `quadOp_hermiteMvLp` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_hermiteMvLp` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadOp_hermiteMvLp
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadOp_hermiteMvLp (c : Fin d → ℝ) (a : Fin d →₀ ℕ)
    (h : hermiteMvLp a ∈ polyGaussCore (d := d)) :
    quadOp c ⟨hermiteMvLp a, h⟩ = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a := by sorry
