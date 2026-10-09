-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_eq_gaussian
-- name    : BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:01:41.69097+00:00
-- url     : https://prove2.me/theorems/40050767-efda-452d-a415-42b2e6b3f5d1
-- title:
--   `BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k = Real.exp (-‖q - k‖ ^ 2 / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlap`.
--
--   `BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k = Real.exp (-‖q - k‖ ^ 2 / 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian`.

-- Generated from ChapterCoherentOverlap.lean — theorem BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap


open scoped BigOperators

noncomputable section


variable {n : ℕ}

theorem BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k = Real.exp (-‖q - k‖ ^ 2 / 2) := by sorry
