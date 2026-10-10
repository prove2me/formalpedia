-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_rotMat_mulVec_clockPsi
-- name    : BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:14:47.377109+00:00
-- url     : https://prove2.me/theorems/ab3df68f-c86d-45df-b6a9-0f5b38be522f
-- title:
--   `BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi` (t a : ℝ) : (rotMat a).mulVec (clockPsi t) = clockPsi (t + a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi` (t a : ℝ) : (rotMat a).mulVec (clockPsi t) = clockPsi (t + a)
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Definitions.Def_ChapterEulerDensityMatrix
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ChapterEulerDensityMatrix
open BookProof.FullQuadratic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi (t a : ℝ) :
    (rotMat a).mulVec (clockPsi t) = clockPsi (t + a) := by sorry
