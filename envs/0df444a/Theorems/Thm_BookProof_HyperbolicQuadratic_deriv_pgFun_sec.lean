-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_deriv_pgFun_sec
-- name    : BookProof.HyperbolicQuadratic.deriv_pgFun_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:02:48.869119+00:00
-- url     : https://prove2.me/theorems/e6752157-5d9d-4b97-b447-1de3dc274aa5
-- title:
--   The Lean 4 theorem `deriv_pgFun_sec` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deriv_pgFun_sec` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.deriv_pgFun_sec
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.deriv_pgFun_sec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (t : ℝ) :
    deriv (fun s : ℝ => pgFun p (sec i x s)) t = pgFun (dPoly i p) (sec i x t) := by sorry
