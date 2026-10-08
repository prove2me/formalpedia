-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_bornMeasure_iUnion
-- name    : BookProof.ChapterBornMeasure.bornMeasure_iUnion
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:57:02.866014+00:00
-- url     : https://prove2.me/theorems/ed34ef18-d864-4494-9912-43169e5330ae
-- title:
--   `BookProof.ChapterBornMeasure.bornMeasure_iUnion` (psi : Lp ℂ 2 μ) {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Function.onFun Disjoint s)) : bornMeasure psi (⋃
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.bornMeasure_iUnion` (psi : Lp ℂ 2 μ) {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Function.onFun Disjoint s)) : bornMeasure psi (⋃ n, s n) = ∑' n, bornMeasure psi (s n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.bornMeasure_iUnion`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.bornMeasure_iUnion
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.bornMeasure_iUnion (psi : Lp ℂ 2 μ) {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Function.onFun Disjoint s)) :
    bornMeasure psi (⋃ n, s n) = ∑' n, bornMeasure psi (s n) := by sorry
