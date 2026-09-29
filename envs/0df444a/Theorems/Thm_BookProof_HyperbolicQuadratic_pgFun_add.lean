-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_pgFun_add
-- name    : BookProof.HyperbolicQuadratic.pgFun_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:19.935365+00:00
-- url     : https://prove2.me/theorems/bd1969d2-642f-4d2b-83aa-2913aaec63ea
-- title:
--   The Lean 4 theorem `pgFun_add` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFun_add` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.pgFun_add
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.pgFun_add (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (p + q) x = pgFun p x + pgFun q x := by sorry
