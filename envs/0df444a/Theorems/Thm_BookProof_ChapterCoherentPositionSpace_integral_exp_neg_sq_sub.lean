-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentPositionSpace_integral_exp_neg_sq_sub
-- name    : BookProof.ChapterCoherentPositionSpace.integral_exp_neg_sq_sub
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:03:54.365982+00:00
-- url     : https://prove2.me/theorems/ee255d15-1db3-4680-977b-3361ec975fc2
-- title:
--   `BookProof.ChapterCoherentPositionSpace.integral_exp_neg_sq_sub` (c : ℝ) : (∫ x : ℝ, Real.exp (-(x - c) ^ 2)) = Real.sqrt Real.pi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentPositionSpace`.
--
--   `BookProof.ChapterCoherentPositionSpace.integral_exp_neg_sq_sub` (c : ℝ) : (∫ x : ℝ, Real.exp (-(x - c) ^ 2)) = Real.sqrt Real.pi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentPositionSpace.integral_exp_neg_sq_sub`.

-- Generated from ChapterCoherentPositionSpace.lean — theorem BookProof.ChapterCoherentPositionSpace.integral_exp_neg_sq_sub
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
open BookProof.ChapterCoherentPositionSpace


open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

theorem BookProof.ChapterCoherentPositionSpace.integral_exp_neg_sq_sub (c : ℝ) :
    (∫ x : ℝ, Real.exp (-(x - c) ^ 2)) = Real.sqrt Real.pi := by sorry
