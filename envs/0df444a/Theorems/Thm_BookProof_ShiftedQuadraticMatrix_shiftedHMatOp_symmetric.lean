-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_symmetric
-- name    : BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:47:27.928985+00:00
-- url     : https://prove2.me/theorems/28348094-a0df-4bd7-94a5-342ffd190a91
-- title:
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) : SymmetricOn (polyGaussCoreT (matShiftVec A b) (matBoostVec A b')) (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
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
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCoreT (matShiftVec A b) (matBoostVec A b'))
      (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b') := by sorry
