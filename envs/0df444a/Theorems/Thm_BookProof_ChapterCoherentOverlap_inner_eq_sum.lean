-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlap_inner_eq_sum
-- name    : BookProof.ChapterCoherentOverlap.inner_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:58:42.505285+00:00
-- url     : https://prove2.me/theorems/86ac7587-97cd-436c-aff2-462f0f6b275b
-- title:
--   `BookProof.ChapterCoherentOverlap.inner_eq_sum` (q k : EuclideanSpace ℝ (Fin n)) : inner ℝ q k = ∑ i, q i * k i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlap`.
--
--   `BookProof.ChapterCoherentOverlap.inner_eq_sum` (q k : EuclideanSpace ℝ (Fin n)) : inner ℝ q k = ∑ i, q i * k i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlap.inner_eq_sum`.

-- Generated from ChapterCoherentOverlap.lean — theorem BookProof.ChapterCoherentOverlap.inner_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap


open scoped BigOperators

noncomputable section


variable {n : ℕ}

theorem BookProof.ChapterCoherentOverlap.inner_eq_sum (q k : EuclideanSpace ℝ (Fin n)) :
    inner ℝ q k = ∑ i, q i * k i := by sorry
