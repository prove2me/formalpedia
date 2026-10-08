-- Prove2me | Theorems.Thm_BookProof_ChapterF3_disjoint_support_inner_zero
-- name    : BookProof.ChapterF3.disjoint_support_inner_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:49:21.343317+00:00
-- url     : https://prove2.me/theorems/79102d2c-8e46-46c3-8cae-a26cd94142bc
-- title:
--   `BookProof.ChapterF3.disjoint_support_inner_zero` {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (f g : α → ℂ) (h : Disjoint (Function.support f) (Function.support g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.disjoint_support_inner_zero` {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (f g : α → ℂ) (h : Disjoint (Function.support f) (Function.support g)) : ∫ x, (starRingEnd ℂ) (f x) * g x ∂μ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.disjoint_support_inner_zero`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.disjoint_support_inner_zero
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

theorem BookProof.ChapterF3.disjoint_support_inner_zero {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f g : α → ℂ) (h : Disjoint (Function.support f) (Function.support g)) :
    ∫ x, (starRingEnd ℂ) (f x) * g x ∂μ = 0 := by sorry
