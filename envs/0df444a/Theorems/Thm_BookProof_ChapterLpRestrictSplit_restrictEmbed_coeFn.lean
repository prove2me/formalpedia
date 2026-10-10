-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_coeFn
-- name    : BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:46:47.501831+00:00
-- url     : https://prove2.me/theorems/e6c283c0-ea2c-46f8-b5f4-df6a627968d3
-- title:
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn` {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 (mu.restrict A)) : (restrictEmbed hA u : α → ℂ) =ᵐ[mu] A.indicator (u : α → ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn` {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 (mu.restrict A)) : (restrictEmbed hA u : α → ℂ) =ᵐ[mu] A.indicator (u : α → ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 (mu.restrict A)) :
    (restrictEmbed hA u : α → ℂ) =ᵐ[mu] A.indicator (u : α → ℂ) := by sorry
