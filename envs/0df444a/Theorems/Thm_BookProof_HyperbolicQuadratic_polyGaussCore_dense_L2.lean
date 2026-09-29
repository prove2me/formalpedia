-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_polyGaussCore_dense_L2
-- name    : BookProof.HyperbolicQuadratic.polyGaussCore_dense_L2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T06:59:53.329537+00:00
-- url     : https://prove2.me/theorems/4090457e-afe3-4e29-b32e-07f7ee890a42
-- title:
--   The Lean 4 theorem `polyGaussCore_dense_L2` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polyGaussCore_dense_L2` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.polyGaussCore_dense_L2
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.polyGaussCore_dense_L2 :
    Dense ((polyGaussCore (d := d) : Submodule ℂ (L2d d)) : Set (L2d d)) := by sorry
