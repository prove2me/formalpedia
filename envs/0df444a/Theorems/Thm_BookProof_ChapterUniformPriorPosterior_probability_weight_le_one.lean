-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPriorPosterior_probability_weight_le_one
-- name    : BookProof.ChapterUniformPriorPosterior.probability_weight_le_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:30:46.215042+00:00
-- url     : https://prove2.me/theorems/353687a5-9efe-4b9d-a5ac-09a3b9d60e17
-- title:
--   `BookProof.ChapterUniformPriorPosterior.probability_weight_le_one` (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1) (x : Hyp) : q x ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPriorPosterior`.
--
--   `BookProof.ChapterUniformPriorPosterior.probability_weight_le_one` (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1) (x : Hyp) : q x ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPriorPosterior.probability_weight_le_one`.

-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.probability_weight_le_one
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

theorem BookProof.ChapterUniformPriorPosterior.probability_weight_le_one (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hq_sum : ∑ x, q x = 1) (x : Hyp) : q x ≤ 1 := by sorry
