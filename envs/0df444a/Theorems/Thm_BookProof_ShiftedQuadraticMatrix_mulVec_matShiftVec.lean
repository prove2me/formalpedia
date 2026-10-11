-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_mulVec_matShiftVec
-- name    : BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:46:39.732726+00:00
-- url     : https://prove2.me/theorems/4bbc1919-0829-4d80-b1a7-a7ab13afbdaa
-- title:
--   `BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec` {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det) (b : Fin d → ℝ) (i : Fin d) : ∑ j, A i j * (matShiftVec A b) j = -2 * b i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec` {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det) (b : Fin d → ℝ) (i : Fin d) : ∑ j, A i j * (matShiftVec A b) j = -2 * b i
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
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

theorem BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det)
    (b : Fin d → ℝ) (i : Fin d) :
    ∑ j, A i j * (matShiftVec A b) j = -2 * b i := by sorry
