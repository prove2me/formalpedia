-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_pgFun_smul
-- name    : BookProof.HyperbolicQuadratic.pgFun_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:50.684883+00:00
-- url     : https://prove2.me/theorems/72ad59ab-7ce0-4d89-a634-dbf7c84db6a8
-- title:
--   The Lean 4 theorem `pgFun_smul` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFun_smul` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.pgFun_smul
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.pgFun_smul (r : ℂ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (r • p) x = r * pgFun p x := by sorry
