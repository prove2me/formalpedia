-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_innerC_eq_sum
-- name    : BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:00:22.192159+00:00
-- url     : https://prove2.me/theorems/91fc3973-7f2e-45a3-a3a0-5bea33cb0a5f
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum` (q k : EuclideanSpace ℂ (Fin n)) : inner ℂ q k = ∑ i, (starRingEnd ℂ) (q i) * k i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum` (q k : EuclideanSpace ℂ (Fin n)) : inner ℂ q k = ∑ i, (starRingEnd ℂ) (q i) * k i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum (q k : EuclideanSpace ℂ (Fin n)) :
    inner ℂ q k = ∑ i, (starRingEnd ℂ) (q i) * k i := by sorry
