-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_preserves_prob_iff_isColumnStochastic
-- name    : BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:55:54.215264+00:00
-- url     : https://prove2.me/theorems/1b7811d5-3f7e-4019-8b47-d9d0698dafb9
-- title:
--   `BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic` (M : Matrix (Fin 2) (Fin 2) ℝ) : (∀ v, IsProbabilityVector v → IsProbabilityVector (M.mulVec v)) ↔ IsCo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic` (M : Matrix (Fin 2) (Fin 2) ℝ) : (∀ v, IsProbabilityVector v → IsProbabilityVector (M.mulVec v)) ↔ IsColumnStochastic M
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ v, IsProbabilityVector v → IsProbabilityVector (M.mulVec v))
      ↔ IsColumnStochastic M := by sorry
