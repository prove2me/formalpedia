-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_polyGaussCore_dense_L2
-- name    : BookProof.QuadraticRotation.polyGaussCore_dense_L2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:25:53.997221+00:00
-- url     : https://prove2.me/theorems/b8a2a895-5945-4c6b-b14d-668344a357d7
-- title:
--   The Lean 4 theorem `polyGaussCore_dense_L2` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polyGaussCore_dense_L2` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.polyGaussCore_dense_L2
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

theorem BookProof.QuadraticRotation.polyGaussCore_dense_L2 :
    Dense ((polyGaussCore (d := d) : Submodule ℂ (L2d d)) : Set (L2d d)) := by sorry
