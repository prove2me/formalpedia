-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_diagonal_degenerate_essentiallySelfAdjoint
-- name    : BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:25:59.765978+00:00
-- url     : https://prove2.me/theorems/399e05ba-d0d3-41ba-bf14-9bce8cd10460
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint` (c b b' : Fin d → ℝ) (hb : ∀ i, c i = 0 → b i = 0) (hb' : ∀ i, c i = 0 → b' i = 0) : EssentiallySe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint` (c b b' : Fin d → ℝ) (hb : ∀ i, c i = 0 → b i = 0) (hb' : ∀ i, c i = 0 → b' i = 0) : EssentiallySelfAdjointOn (polyGaussCoreT (diagShiftVec c fun i => -2 * b i) (diagShiftVec c fun i => -(b' i) / 2)) (shiftedHMatOp (diagShiftVec c fun i => -2 * b i) (diagShiftVec c fun i => -(b' i) / 2) (Matrix.diagonal c) b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.ShiftedHermiteCore
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

theorem BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint (c b b' : Fin d → ℝ)
    (hb : ∀ i, c i = 0 → b i = 0) (hb' : ∀ i, c i = 0 → b' i = 0) :
    EssentiallySelfAdjointOn
      (polyGaussCoreT (diagShiftVec c fun i => -2 * b i)
        (diagShiftVec c fun i => -(b' i) / 2))
      (shiftedHMatOp (diagShiftVec c fun i => -2 * b i)
        (diagShiftVec c fun i => -(b' i) / 2) (Matrix.diagonal c) b b') := by sorry
