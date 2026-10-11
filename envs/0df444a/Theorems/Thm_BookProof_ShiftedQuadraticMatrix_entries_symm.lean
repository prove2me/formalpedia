-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_entries_symm
-- name    : BookProof.ShiftedQuadraticMatrix.entries_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:47:46.258822+00:00
-- url     : https://prove2.me/theorems/0c708272-431f-41fa-bb9a-53867366e766
-- title:
--   `BookProof.ShiftedQuadraticMatrix.entries_symm` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (i j : Fin d) : A i j = A j i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.entries_symm` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (i j : Fin d) : A i j = A j i
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.entries_symm`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.entries_symm
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

theorem BookProof.ShiftedQuadraticMatrix.entries_symm {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (i j : Fin d) :
    A i j = A j i := by sorry
