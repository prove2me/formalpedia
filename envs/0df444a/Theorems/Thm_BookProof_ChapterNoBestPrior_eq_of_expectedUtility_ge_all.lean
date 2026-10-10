-- Prove2me | Theorems.Thm_BookProof_ChapterNoBestPrior_eq_of_expectedUtility_ge_all
-- name    : BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:21.1602+00:00
-- url     : https://prove2.me/theorems/83edd88e-d368-43f0-a690-6c06adcfe171
-- title:
--   `BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all` (p q : Hyp → ℝ) (h : ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u) : p = q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNoBestPrior`.
--
--   `BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all` (p q : Hyp → ℝ) (h : ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u) : p = q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all`.

-- Generated from ChapterNoBestPrior.lean — theorem BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all
import Mathlib
import Definitions.Def_ChapterNoBestPrior
open BookProof.ChapterNoBestPrior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp]

theorem BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all (p q : Hyp → ℝ)
    (h : ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u) :
    p = q := by sorry
