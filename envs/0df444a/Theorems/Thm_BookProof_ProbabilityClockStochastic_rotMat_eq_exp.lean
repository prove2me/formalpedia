-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_rotMat_eq_exp
-- name    : BookProof.ProbabilityClockStochastic.rotMat_eq_exp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:15:16.112984+00:00
-- url     : https://prove2.me/theorems/1db0cbe7-53d2-43d3-99e6-ef63f20c615c
-- title:
--   `BookProof.ProbabilityClockStochastic.rotMat_eq_exp` (a : ℝ) : NormedSpace.exp (a • Jgen) = rotMat a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.rotMat_eq_exp` (a : ℝ) : NormedSpace.exp (a • Jgen) = rotMat a
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.rotMat_eq_exp`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.rotMat_eq_exp
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Definitions.Def_ChapterEulerGenericDensity
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ChapterEulerGenericDensity
open BookProof.FullQuadratic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.rotMat_eq_exp (a : ℝ) :
    NormedSpace.exp (a • Jgen) = rotMat a := by sorry
