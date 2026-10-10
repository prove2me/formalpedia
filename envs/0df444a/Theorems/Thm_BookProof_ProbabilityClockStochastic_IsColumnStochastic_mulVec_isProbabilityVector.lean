-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_IsColumnStochastic_mulVec_isProbabilityVector
-- name    : BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:55:44.364427+00:00
-- url     : https://prove2.me/theorems/addc9e5b-4589-497f-b2c1-336bd0227bec
-- title:
--   `BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector` {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M) {v : Fin 2 → ℝ} (hv : IsProbabilityV
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector` {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M) {v : Fin 2 → ℝ} (hv : IsProbabilityVector v) : IsProbabilityVector (M.mulVec v)
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M)
    {v : Fin 2 → ℝ} (hv : IsProbabilityVector v) :
    IsProbabilityVector (M.mulVec v) := by sorry
