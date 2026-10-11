-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_shiftedHMatOp_symmetric_of_equilibrium
-- name    : BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:41.505975+00:00
-- url     : https://prove2.me/theorems/85c8e639-4315-44fc-824e-5cabb8790662
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (b b' : Fin d → ℝ) (a k : Vd d) (ha : ∀ i, ∑ j, A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (b b' : Fin d → ℝ) (a k : Vd d) (ha : ∀ i, ∑ j, A i j * a j = -2 * b i) (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2) : SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium
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

theorem BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (b b' : Fin d → ℝ) (a k : Vd d)
    (ha : ∀ i, ∑ j, A i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2) :
    SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') := by sorry
