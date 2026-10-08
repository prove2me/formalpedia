-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentPositionSpace_integral_exp_mul_exp
-- name    : BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:03:54.189984+00:00
-- url     : https://prove2.me/theorems/9f733ec6-6c15-4abf-b14d-f65f0a4605d5
-- title:
--   `BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp` (a b : ℝ) : (∫ x : ℝ, Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2)) = Real.exp (-(a - b) ^ 2 / 4) * Real.
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentPositionSpace`.
--
--   `BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp` (a b : ℝ) : (∫ x : ℝ, Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2)) = Real.exp (-(a - b) ^ 2 / 4) * Real.sqrt Real.pi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp`.

-- Generated from ChapterCoherentPositionSpace.lean — theorem BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
open BookProof.ChapterCoherentPositionSpace


open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

theorem BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp (a b : ℝ) :
    (∫ x : ℝ, Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2))
      = Real.exp (-(a - b) ^ 2 / 4) * Real.sqrt Real.pi := by sorry
