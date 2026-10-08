-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlap_norm_sub_sq_expand
-- name    : BookProof.ChapterCoherentOverlap.norm_sub_sq_expand
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:59:08.928254+00:00
-- url     : https://prove2.me/theorems/bc4db9e8-c819-4b70-8020-a9c95d4785cd
-- title:
--   `BookProof.ChapterCoherentOverlap.norm_sub_sq_expand` (q k : EuclideanSpace ℝ (Fin n)) : ‖q - k‖ ^ 2 = ‖q‖ ^ 2 + ‖k‖ ^ 2 - 2 * inner ℝ q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlap`.
--
--   `BookProof.ChapterCoherentOverlap.norm_sub_sq_expand` (q k : EuclideanSpace ℝ (Fin n)) : ‖q - k‖ ^ 2 = ‖q‖ ^ 2 + ‖k‖ ^ 2 - 2 * inner ℝ q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlap.norm_sub_sq_expand`.

-- Generated from ChapterCoherentOverlap.lean — theorem BookProof.ChapterCoherentOverlap.norm_sub_sq_expand
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap


open scoped BigOperators

noncomputable section


variable {n : ℕ}

theorem BookProof.ChapterCoherentOverlap.norm_sub_sq_expand (q k : EuclideanSpace ℝ (Fin n)) :
    ‖q - k‖ ^ 2 = ‖q‖ ^ 2 + ‖k‖ ^ 2 - 2 * inner ℝ q k := by sorry
