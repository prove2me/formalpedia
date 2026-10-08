-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentOverlapC_eq_sum
-- name    : BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:00:26.025622+00:00
-- url     : https://prove2.me/theorems/827330df-e4b7-4912-9ada-1f54c9a01861
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum` (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC q k = Complex.exp (((-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 : ℝ) : ℂ) + ∑
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum` (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC q k = Complex.exp (((-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 : ℝ) : ℂ) + ∑ i, (starRingEnd ℂ) (q i) * k i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC q k =
      Complex.exp (((-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 : ℝ) : ℂ)
        + ∑ i, (starRingEnd ℂ) (q i) * k i) := by sorry
