-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_deriv2_pgFun_sec
-- name    : BookProof.HyperbolicQuadratic.deriv2_pgFun_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:04:58.995462+00:00
-- url     : https://prove2.me/theorems/782c27ac-c76f-4a95-93b6-afb382138401
-- title:
--   The Lean 4 theorem `deriv2_pgFun_sec` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deriv2_pgFun_sec` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.deriv2_pgFun_sec
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.deriv2_pgFun_sec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => pgFun p (sec i x s)) t) (x i)
      = pgFun (dPoly i (dPoly i p)) x := by sorry
