-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlap_norm_sq_eq_sum
-- name    : BookProof.ChapterCoherentOverlap.norm_sq_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:58:40.645642+00:00
-- url     : https://prove2.me/theorems/ab4eeabe-5b76-4435-a438-76198dc53182
-- title:
--   `BookProof.ChapterCoherentOverlap.norm_sq_eq_sum` (q : EuclideanSpace ℝ (Fin n)) : ‖q‖ ^ 2 = ∑ i, q i * q i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlap`.
--
--   `BookProof.ChapterCoherentOverlap.norm_sq_eq_sum` (q : EuclideanSpace ℝ (Fin n)) : ‖q‖ ^ 2 = ∑ i, q i * q i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlap.norm_sq_eq_sum`.

-- Generated from ChapterCoherentOverlap.lean — theorem BookProof.ChapterCoherentOverlap.norm_sq_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap


open scoped BigOperators

noncomputable section


variable {n : ℕ}

theorem BookProof.ChapterCoherentOverlap.norm_sq_eq_sum (q : EuclideanSpace ℝ (Fin n)) :
    ‖q‖ ^ 2 = ∑ i, q i * q i := by sorry
