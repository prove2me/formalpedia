-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_stochastic_uniform_to_deterministic_not_isUnit
-- name    : BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:56:37.070008+00:00
-- url     : https://prove2.me/theorems/00618dcd-e79c-4f2d-b125-66bc12f9cedc
-- title:
--   `BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit` {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M) (hMap : M.mulVec ![1 / 2, 1 / 2] =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit` {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M) (hMap : M.mulVec ![1 / 2, 1 / 2] = ![1, 0]) : ¬ IsUnit M
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M)
    (hMap : M.mulVec ![1 / 2, 1 / 2] = ![1, 0]) : ¬ IsUnit M := by sorry
