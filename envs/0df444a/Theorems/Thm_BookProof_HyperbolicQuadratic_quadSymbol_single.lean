-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadSymbol_single
-- name    : BookProof.HyperbolicQuadratic.quadSymbol_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:36.735749+00:00
-- url     : https://prove2.me/theorems/5db4ab04-ef2d-4c18-a2f3-56e9177a8237
-- title:
--   The Lean 4 theorem `quadSymbol_single` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadSymbol_single` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadSymbol_single
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadSymbol_single (c : Fin d → ℝ) (i : Fin d) (n : ℕ) :
    quadSymbol c (Finsupp.single i n) = c i * (n : ℝ) + ∑ j, c j * (1/2) := by sorry
