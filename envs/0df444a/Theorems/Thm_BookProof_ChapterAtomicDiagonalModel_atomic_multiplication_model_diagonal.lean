-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDiagonalModel_atomic_multiplication_model_diagonal
-- name    : BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:33:47.541126+00:00
-- url     : https://prove2.me/theorems/1bf4e7e8-0fa7-46e7-a8c0-032f48fa5fde
-- title:
--   `BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal` (hpure : mu (atomSet mu)ᶜ = 0) : ∃ B : HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu), ∀ (g : α → ℂ) (hg : MemL
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDiagonalModel`.
--
--   `BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal` (hpure : mu (atomSet mu)ᶜ = 0) : ∃ B : HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu), ∀ (g : α → ℂ) (hg : MemLp g ⊤ mu) (a : atomSet mu), multOp g hg (B a) = g (a : α) • B a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal`.

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Mathlib
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterAtomicDiagonalModel


noncomputable section

open MeasureTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (mu : Measure α) [IsFiniteMeasure mu]

theorem BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal (hpure : mu (atomSet mu)ᶜ = 0) :
    ∃ B : HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu),
      ∀ (g : α → ℂ) (hg : MemLp g ⊤ mu) (a : atomSet mu),
        multOp g hg (B a) = g (a : α) • B a := by sorry
