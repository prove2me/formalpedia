-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDiagonalModel_multOp_atomVec
-- name    : BookProof.ChapterAtomicDiagonalModel.multOp_atomVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:33:08.972965+00:00
-- url     : https://prove2.me/theorems/df1bb4e7-06b6-4d03-92ec-a6b1190f95ad
-- title:
--   `BookProof.ChapterAtomicDiagonalModel.multOp_atomVec` {g : α → ℂ} (hg : MemLp g ⊤ mu) (a : atomSet mu) : multOp g hg (atomVec mu a) = g (a : α) • atomVec mu a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDiagonalModel`.
--
--   `BookProof.ChapterAtomicDiagonalModel.multOp_atomVec` {g : α → ℂ} (hg : MemLp g ⊤ mu) (a : atomSet mu) : multOp g hg (atomVec mu a) = g (a : α) • atomVec mu a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDiagonalModel.multOp_atomVec`.

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.multOp_atomVec
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

theorem BookProof.ChapterAtomicDiagonalModel.multOp_atomVec {g : α → ℂ} (hg : MemLp g ⊤ mu) (a : atomSet mu) :
    multOp g hg (atomVec mu a) = g (a : α) • atomVec mu a := by sorry
