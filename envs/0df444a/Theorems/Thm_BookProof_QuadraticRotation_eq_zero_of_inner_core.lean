-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_eq_zero_of_inner_core
-- name    : BookProof.QuadraticRotation.eq_zero_of_inner_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:27:01.364208+00:00
-- url     : https://prove2.me/theorems/7f87e95f-2f77-4b6e-bed4-ab76dc603714
-- title:
--   The Lean 4 theorem `eq_zero_of_inner_core` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eq_zero_of_inner_core` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.eq_zero_of_inner_core
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.eq_zero_of_inner_core (w : L2d d)
    (h : ∀ u ∈ polyGaussCore (d := d), (inner ℂ u w : ℂ) = 0) : w = 0 := by sorry
