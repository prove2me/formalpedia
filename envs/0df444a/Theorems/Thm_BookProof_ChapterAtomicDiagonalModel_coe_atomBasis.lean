-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDiagonalModel_coe_atomBasis
-- name    : BookProof.ChapterAtomicDiagonalModel.coe_atomBasis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:34:24.972005+00:00
-- url     : https://prove2.me/theorems/d84cf42f-8c2b-4c4b-bcbd-206ac613dd95
-- title:
--   `BookProof.ChapterAtomicDiagonalModel.coe_atomBasis` (hpure : mu (atomSet mu)ᶜ = 0) : ⇑(atomBasis mu hpure) = atomVec mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDiagonalModel`.
--
--   `BookProof.ChapterAtomicDiagonalModel.coe_atomBasis` (hpure : mu (atomSet mu)ᶜ = 0) : ⇑(atomBasis mu hpure) = atomVec mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDiagonalModel.coe_atomBasis`.

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.coe_atomBasis
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

theorem BookProof.ChapterAtomicDiagonalModel.coe_atomBasis (hpure : mu (atomSet mu)ᶜ = 0) :
    ⇑(atomBasis mu hpure) = atomVec mu := by sorry
