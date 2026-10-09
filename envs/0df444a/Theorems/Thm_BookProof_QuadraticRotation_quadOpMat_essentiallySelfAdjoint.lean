-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_essentiallySelfAdjoint
-- name    : BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:02:35.121919+00:00
-- url     : https://prove2.me/theorems/02bd94ae-46df-47bd-a12f-6fc4276aa388
-- title:
--   The Lean 4 theorem `quadOpMat_essentiallySelfAdjoint` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOpMat A) := by sorry
