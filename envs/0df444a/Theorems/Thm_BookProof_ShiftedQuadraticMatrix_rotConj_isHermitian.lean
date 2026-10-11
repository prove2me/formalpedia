-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_rotConj_isHermitian
-- name    : BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:49:11.90424+00:00
-- url     : https://prove2.me/theorems/4f8430b6-577a-4c7e-ac15-2530774f0bab
-- title:
--   `BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian` (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) : (rotConj O c).IsHermitian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian` (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) : (rotConj O c).IsHermitian
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian
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

theorem BookProof.ShiftedQuadraticMatrix.rotConj_isHermitian (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    (rotConj O c).IsHermitian := by sorry
