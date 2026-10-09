-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_bornMeasure_apply
-- name    : BookProof.ChapterBornMeasure.bornMeasure_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:56:22.273198+00:00
-- url     : https://prove2.me/theorems/0f050eb3-4a81-4cf6-b40f-c34ab6e09567
-- title:
--   `BookProof.ChapterBornMeasure.bornMeasure_apply` (psi : Lp ℂ 2 μ) {s : Set α} (hs : MeasurableSet s) : bornMeasure psi s = ∫⁻ x in s, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.bornMeasure_apply` (psi : Lp ℂ 2 μ) {s : Set α} (hs : MeasurableSet s) : bornMeasure psi s = ∫⁻ x in s, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.bornMeasure_apply`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.bornMeasure_apply
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.bornMeasure_apply (psi : Lp ℂ 2 μ) {s : Set α} (hs : MeasurableSet s) :
    bornMeasure psi s = ∫⁻ x in s, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ := by sorry
