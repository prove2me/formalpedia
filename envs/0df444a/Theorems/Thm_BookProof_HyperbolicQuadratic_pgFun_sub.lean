-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_pgFun_sub
-- name    : BookProof.HyperbolicQuadratic.pgFun_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:37.522707+00:00
-- url     : https://prove2.me/theorems/1a23da95-0adf-44b0-a059-a47ff2b13920
-- title:
--   The Lean 4 theorem `pgFun_sub` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFun_sub` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.pgFun_sub
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.pgFun_sub (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (p - q) x = pgFun p x - pgFun q x := by sorry
