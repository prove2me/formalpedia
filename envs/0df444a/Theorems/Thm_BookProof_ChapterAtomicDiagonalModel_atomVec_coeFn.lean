-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDiagonalModel_atomVec_coeFn
-- name    : BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:32:56.896033+00:00
-- url     : https://prove2.me/theorems/8f05ab45-ce82-4726-a8bc-2f8b1c65ebd5
-- title:
--   `BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn` (a : atomSet mu) : (atomVec mu a : α → ℂ) =ᵐ[mu] fun x => (((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ) : ℂ) * Set.indicator {(a : α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDiagonalModel`.
--
--   `BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn` (a : atomSet mu) : (atomVec mu a : α → ℂ) =ᵐ[mu] fun x => (((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ) : ℂ) * Set.indicator {(a : α)} (fun _ => (1 : ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn`.

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAtomicDiagonalModel
open BookProof.ChapterAtomicDiagonalModel


noncomputable section

open MeasureTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (mu : Measure α) [IsFiniteMeasure mu]

theorem BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn (a : atomSet mu) :
    (atomVec mu a : α → ℂ) =ᵐ[mu] fun x =>
      (((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ) : ℂ) *
        Set.indicator {(a : α)} (fun _ => (1 : ℂ)) x := by sorry
