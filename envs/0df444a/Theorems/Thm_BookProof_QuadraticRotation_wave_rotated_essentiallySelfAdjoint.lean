-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_wave_rotated_essentiallySelfAdjoint
-- name    : BookProof.QuadraticRotation.wave_rotated_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:31:55.364269+00:00
-- url     : https://prove2.me/theorems/2ad1014d-d8ae-43f4-89b6-5b96bfae6949
-- title:
--   The Lean 4 theorem `wave_rotated_essentiallySelfAdjoint` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_rotated_essentiallySelfAdjoint` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.wave_rotated_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.wave_rotated_essentiallySelfAdjoint {n : ℕ}
    {O : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ} (hO : Oᵀ * O = 1) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 1 + n))
      (quadOpMat (rotConj O (minkowskiCoeff n))) := by sorry
