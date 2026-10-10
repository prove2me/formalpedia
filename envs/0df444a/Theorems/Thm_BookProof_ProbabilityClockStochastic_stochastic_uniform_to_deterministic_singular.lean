-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_stochastic_uniform_to_deterministic_singular
-- name    : BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:56:39.570394+00:00
-- url     : https://prove2.me/theorems/458bbc4c-110a-4228-8487-479d0a6e65db
-- title:
--   `BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular` {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M) (hMap : M.mulVec ![1 / 2, 1 / 2] = ![
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular` {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M) (hMap : M.mulVec ![1 / 2, 1 / 2] = ![1, 0]) : M.det = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M)
    (hMap : M.mulVec ![1 / 2, 1 / 2] = ![1, 0]) : M.det = 0 := by sorry
