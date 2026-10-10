-- Prove2me | Theorems.Thm_BookProof_ChapterNoBestPrior_not_uniformly_better
-- name    : BookProof.ChapterNoBestPrior.not_uniformly_better
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:31.946978+00:00
-- url     : https://prove2.me/theorems/06fd6dfc-1680-4bdf-bf47-8b74a906f802
-- title:
--   `BookProof.ChapterNoBestPrior.not_uniformly_better` (p q : Hyp → ℝ) (hpq : p ≠ q) : ¬ ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNoBestPrior`.
--
--   `BookProof.ChapterNoBestPrior.not_uniformly_better` (p q : Hyp → ℝ) (hpq : p ≠ q) : ¬ ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNoBestPrior.not_uniformly_better`.

-- Generated from ChapterNoBestPrior.lean — theorem BookProof.ChapterNoBestPrior.not_uniformly_better
import Mathlib
import Definitions.Def_ChapterNoBestPrior
open BookProof.ChapterNoBestPrior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp]

theorem BookProof.ChapterNoBestPrior.not_uniformly_better (p q : Hyp → ℝ) (hpq : p ≠ q) :
    ¬ ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u := by sorry
