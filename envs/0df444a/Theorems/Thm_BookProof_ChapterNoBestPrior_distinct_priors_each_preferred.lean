-- Prove2me | Theorems.Thm_BookProof_ChapterNoBestPrior_distinct_priors_each_preferred
-- name    : BookProof.ChapterNoBestPrior.distinct_priors_each_preferred
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:30.386613+00:00
-- url     : https://prove2.me/theorems/0de09d20-f192-4af3-aafa-13c5fa371c22
-- title:
--   `BookProof.ChapterNoBestPrior.distinct_priors_each_preferred` (p q : Hyp → ℝ) (hpq : p ≠ q) : (∃ u, expectedUtility q u < expectedUtility p u) ∧ ∃ v, expectedUtility p v < expected
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNoBestPrior`.
--
--   `BookProof.ChapterNoBestPrior.distinct_priors_each_preferred` (p q : Hyp → ℝ) (hpq : p ≠ q) : (∃ u, expectedUtility q u < expectedUtility p u) ∧ ∃ v, expectedUtility p v < expectedUtility q v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNoBestPrior.distinct_priors_each_preferred`.

-- Generated from ChapterNoBestPrior.lean — theorem BookProof.ChapterNoBestPrior.distinct_priors_each_preferred
import Mathlib
import Definitions.Def_ChapterNoBestPrior
open BookProof.ChapterNoBestPrior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp]

theorem BookProof.ChapterNoBestPrior.distinct_priors_each_preferred (p q : Hyp → ℝ) (hpq : p ≠ q) :
    (∃ u, expectedUtility q u < expectedUtility p u) ∧
      ∃ v, expectedUtility p v < expectedUtility q v := by sorry
