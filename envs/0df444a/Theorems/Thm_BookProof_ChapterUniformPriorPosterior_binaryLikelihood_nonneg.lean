-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPriorPosterior_binaryLikelihood_nonneg
-- name    : BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:47:27.395558+00:00
-- url     : https://prove2.me/theorems/d53726f3-35a0-4b97-8cd9-ad643e0ce78d
-- title:
--   `BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg` (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1) (x : Hyp) (observed : Bool) : 0 ≤ binaryLikelihood
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPriorPosterior`.
--
--   `BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg` (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1) (x : Hyp) (observed : Bool) : 0 ≤ binaryLikelihood q x observed
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg`.

-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

theorem BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hq_sum : ∑ x, q x = 1) (x : Hyp) (observed : Bool) :
    0 ≤ binaryLikelihood q x observed := by sorry
