-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_pgLp_hermiteMvLp
-- name    : BookProof.HyperbolicQuadratic.pgLp_hermiteMvLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:45.865067+00:00
-- url     : https://prove2.me/theorems/1278fe14-f4dc-4319-9712-bc0e65ec42b3
-- title:
--   The Lean 4 theorem `pgLp_hermiteMvLp` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgLp_hermiteMvLp` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.pgLp_hermiteMvLp
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.pgLp_hermiteMvLp (a : Fin d →₀ ℕ) :
    pgLp (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a) = hermiteMvLp a := by sorry
