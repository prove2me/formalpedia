-- Prove2me | Theorems.Thm_BookProof_ProbabilityClockStochastic_clockPsi_eq_exp
-- name    : BookProof.ProbabilityClockStochastic.clockPsi_eq_exp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:15:49.094992+00:00
-- url     : https://prove2.me/theorems/8d7bd144-ec6f-4920-a6c6-1e36aa4ae861
-- title:
--   `BookProof.ProbabilityClockStochastic.clockPsi_eq_exp` (t : ℝ) : (NormedSpace.exp (t • Jgen)).mulVec ![1, 0] = clockPsi t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityClockStochastic`.
--
--   `BookProof.ProbabilityClockStochastic.clockPsi_eq_exp` (t : ℝ) : (NormedSpace.exp (t • Jgen)).mulVec ![1, 0] = clockPsi t
--
--   Formalization note: Lean 4 identifier `BookProof.ProbabilityClockStochastic.clockPsi_eq_exp`.

-- Generated from ChapterProbabilityClockStochastic.lean — theorem BookProof.ProbabilityClockStochastic.clockPsi_eq_exp
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Definitions.Def_ChapterEulerDensityMatrix
import Definitions.Def_ChapterEulerGenericDensity
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ChapterEulerDensityMatrix
open BookProof.ChapterEulerGenericDensity
open BookProof.FullQuadratic
open BookProof.ProbabilityClockStochastic



open Matrix
open scoped Norms.Operator

theorem BookProof.ProbabilityClockStochastic.clockPsi_eq_exp (t : ℝ) :
    (NormedSpace.exp (t • Jgen)).mulVec ![1, 0] = clockPsi t := by sorry
