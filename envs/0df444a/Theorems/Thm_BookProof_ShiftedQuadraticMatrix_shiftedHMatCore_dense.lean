-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatCore_dense
-- name    : BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:47:42.039826+00:00
-- url     : https://prove2.me/theorems/584c807d-bdec-46b3-a20c-eaf0fccddcdf
-- title:
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense` {A : Matrix (Fin d) (Fin d) ℝ} (b b' : Fin d → ℝ) : Dense ((polyGaussCoreT (matShiftVec A b) (matBoostVec A b') : Submodule
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense` {A : Matrix (Fin d) (Fin d) ℝ} (b b' : Fin d → ℝ) : Dense ((polyGaussCoreT (matShiftVec A b) (matBoostVec A b') : Submodule ℂ (L2d d)) : Set (L2d d))
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense
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

theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense {A : Matrix (Fin d) (Fin d) ℝ} (b b' : Fin d → ℝ) :
    Dense ((polyGaussCoreT (matShiftVec A b) (matBoostVec A b')
      : Submodule ℂ (L2d d)) : Set (L2d d)) := by sorry
