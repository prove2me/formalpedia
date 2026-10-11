-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_exists_shiftedHMat_esa_of_kernel_orthogonal
-- name    : BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:16.66252+00:00
-- url     : https://prove2.me/theorems/43b95bc5-6870-4e5d-9463-7565934ae7a7
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (b b' : Fin d → ℝ) (hb : ∀ v : Fin d → ℝ, (∀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (b b' : Fin d → ℝ) (hb : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, b i * v i = 0) (hb' : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, b' i * v i = 0) : ∃ a k : Vd d, Dense ((polyGaussCoreT a k : Submodule ℂ (L2d d)) : Set (L2d d)) ∧ SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') ∧ EssentiallySelfAdjointOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') ∧ ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (shiftedHMatOp a k A b b') T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.ShiftedHermiteCore
open BookProof.StoneBridge
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

theorem BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (b b' : Fin d → ℝ)
    (hb : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, b i * v i = 0)
    (hb' : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, b' i * v i = 0) :
    ∃ a k : Vd d,
      Dense ((polyGaussCoreT a k : Submodule ℂ (L2d d)) : Set (L2d d)) ∧
      SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') ∧
      EssentiallySelfAdjointOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') ∧
      ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
        IsSelfAdjointExtension (shiftedHMatOp a k A b b') T.op ∧ IsStoneFlow T U := by sorry
