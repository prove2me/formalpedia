-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_deficiencyTrivialAt
-- name    : BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:47:14.929376+00:00
-- url     : https://prove2.me/theorems/f0a2b585-9ed8-4c9c-b69c-3e0e0abc1a1f
-- title:
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_deficiencyTrivialAt` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ) (hsym
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_deficiencyTrivialAt` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ) (hsym : ∀ i j, rotConj O c i j = rotConj O c j i) (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i) (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCoreT a k) (shiftedHMatOp a k (rotConj O c) b b') z
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_deficiencyTrivialAt`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_deficiencyTrivialAt
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

theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_deficiencyTrivialAt {O : Matrix (Fin d) (Fin d) ℝ}
    (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCoreT a k) (shiftedHMatOp a k (rotConj O c) b b') z := by sorry
