-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_diagonal_mulVec_diagShiftVec
-- name    : BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:41.314189+00:00
-- url     : https://prove2.me/theorems/fcc282b4-cb5f-4441-919d-54df2fbb9aab
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec` {c w : Fin d → ℝ} (hcw : ∀ i, c i = 0 → w i = 0) (i : Fin d) : ∑ j, (Matrix.diagonal c) i j * (diagShiftVec c w)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec` {c w : Fin d → ℝ} (hcw : ∀ i, c i = 0 → w i = 0) (i : Fin d) : ∑ j, (Matrix.diagonal c) i j * (diagShiftVec c w) j = w i
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
open BookProof.ShiftedQuadraticDegenerate



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticDegenerate.diagonal_mulVec_diagShiftVec {c w : Fin d → ℝ} (hcw : ∀ i, c i = 0 → w i = 0)
    (i : Fin d) : ∑ j, (Matrix.diagonal c) i j * (diagShiftVec c w) j = w i := by sorry
