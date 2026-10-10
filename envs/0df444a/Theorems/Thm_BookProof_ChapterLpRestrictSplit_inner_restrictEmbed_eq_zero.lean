-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_inner_restrictEmbed_eq_zero
-- name    : BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:47:16.88773+00:00
-- url     : https://prove2.me/theorems/4bf30a9e-4307-482c-8204-07c8679cd4db
-- title:
--   `BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero` {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (u : Lp ℂ 2 (mu.restrict A)) (v : Lp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero` {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (u : Lp ℂ 2 (mu.restrict A)) (v : Lp ℂ 2 (mu.restrict B)) : inner ℂ (restrictEmbed hA u) (restrictEmbed hB v) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (u : Lp ℂ 2 (mu.restrict A)) (v : Lp ℂ 2 (mu.restrict B)) :
    inner ℂ (restrictEmbed hA u) (restrictEmbed hB v) = 0 := by sorry
