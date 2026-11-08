-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_not_bounded
-- name    : BookProof.QuadraticRotation.quadOpMat_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:31:11.400948+00:00
-- url     : https://prove2.me/theorems/b9de7041-cb19-494b-bf5b-036c57bf39ca
-- title:
--   The Lean 4 theorem `quadOpMat_not_bounded` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOpMat_not_bounded` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadOpMat_not_bounded
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

theorem BookProof.QuadraticRotation.quadOpMat_not_bounded {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (hA0 : A ≠ 0) :
    ¬ ∃ K : ℝ, ∀ f : polyGaussCore (d := d), ‖quadOpMat A f‖ ≤ K * ‖(f : L2d d)‖ := by sorry
