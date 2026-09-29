-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_apply_eq_differential
-- name    : BookProof.HyperbolicQuadratic.quadPoly_apply_eq_differential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:23.513841+00:00
-- url     : https://prove2.me/theorems/faa1f56d-2a5d-45a1-aa77-d28ebf858ac8
-- title:
--   The Lean 4 theorem `quadPoly_apply_eq_differential` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadPoly_apply_eq_differential` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadPoly_apply_eq_differential
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadPoly_apply_eq_differential (c : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ)
    (x : Vd d) :
    pgFun (quadPoly c p) x
      = ∑ i, ((c i : ℝ) : ℂ)
          * (-(deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec i x s)) t) (x i))
            + (((x i : ℝ) : ℂ) ^ 2 / 4) * pgFun p x) := by sorry
