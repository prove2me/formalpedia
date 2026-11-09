-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_diagonal
-- name    : BookProof.QuadraticRotation.quadPolyMat_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:24:45.731865+00:00
-- url     : https://prove2.me/theorems/8011b639-241f-4eba-a2f2-720b8f24939d
-- title:
--   The Lean 4 theorem `quadPolyMat_diagonal` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadPolyMat_diagonal` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadPolyMat_diagonal
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadPolyMat_diagonal (c : Fin d → ℝ) :
    quadPolyMat (Matrix.diagonal c) = quadPoly c := by sorry
