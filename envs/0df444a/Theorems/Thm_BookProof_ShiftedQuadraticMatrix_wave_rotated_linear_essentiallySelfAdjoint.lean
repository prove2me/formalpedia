-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_wave_rotated_linear_essentiallySelfAdjoint
-- name    : BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:48:19.828681+00:00
-- url     : https://prove2.me/theorems/cce13fbd-1733-448e-b5a7-1dc1765fdf7f
-- title:
--   `BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint` (n : ℕ) {O : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ} (hO : Oᵀ * O = 1) (b b' : Fin (1 + n) → ℝ) : Essent
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint` (n : ℕ) {O : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ} (hO : Oᵀ * O = 1) (b b' : Fin (1 + n) → ℝ) : EssentiallySelfAdjointOn (polyGaussCoreT (matShiftVec (rotConj O (minkowskiCoeff n)) b) (matBoostVec (rotConj O (minkowskiCoeff n)) b')) (shiftedHMatOp (matShiftVec (rotConj O (minkowskiCoeff n)) b) (matBoostVec (rotConj O (minkowskiCoeff n)) b') (rotConj O (minkowskiCoeff n)) b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint (n : ℕ)
    {O : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ} (hO : Oᵀ * O = 1)
    (b b' : Fin (1 + n) → ℝ) :
    EssentiallySelfAdjointOn
      (polyGaussCoreT (matShiftVec (rotConj O (minkowskiCoeff n)) b)
        (matBoostVec (rotConj O (minkowskiCoeff n)) b'))
      (shiftedHMatOp (matShiftVec (rotConj O (minkowskiCoeff n)) b)
        (matBoostVec (rotConj O (minkowskiCoeff n)) b')
        (rotConj O (minkowskiCoeff n)) b b') := by sorry
