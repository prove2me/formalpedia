-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPriorPosterior_binaryLikelihood_sum
-- name    : BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:47:58.724979+00:00
-- url     : https://prove2.me/theorems/429454b1-96e0-4d45-915e-a55c5a231d0d
-- title:
--   `BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum` (q : Hyp → ℝ) (x : Hyp) : ∑ observed : Bool, binaryLikelihood q x observed = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPriorPosterior`.
--
--   `BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum` (q : Hyp → ℝ) (x : Hyp) : ∑ observed : Bool, binaryLikelihood q x observed = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum`.

-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

theorem BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum (q : Hyp → ℝ) (x : Hyp) :
    ∑ observed : Bool, binaryLikelihood q x observed = 1 := by sorry
