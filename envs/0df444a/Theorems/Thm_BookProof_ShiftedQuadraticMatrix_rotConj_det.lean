-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_rotConj_det
-- name    : BookProof.ShiftedQuadraticMatrix.rotConj_det
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:48:09.30411+00:00
-- url     : https://prove2.me/theorems/9e5520af-7ac5-4335-bdc7-81a00f82aea3
-- title:
--   `BookProof.ShiftedQuadraticMatrix.rotConj_det` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) : (rotConj O c).det = ∏ i, c i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.rotConj_det` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) : (rotConj O c).det = ∏ i, c i
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.rotConj_det`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.rotConj_det
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

theorem BookProof.ShiftedQuadraticMatrix.rotConj_det {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) :
    (rotConj O c).det = ∏ i, c i := by sorry
