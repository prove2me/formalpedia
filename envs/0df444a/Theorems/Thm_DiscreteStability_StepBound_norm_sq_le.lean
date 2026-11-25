-- Prove2me | Theorems.Thm_DiscreteStability_StepBound_norm_sq_le
-- name    : DiscreteStability.StepBound.norm_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:27.320029+00:00
-- url     : https://prove2.me/theorems/733e0dfc-470f-5992-b564-d1ad239b8543
-- title:
--   Step Bound: norm sq le
-- statement:
--   `P² ⪯ λₙ(P) P`: `‖P u‖² ≤ hi ⟪P u, u⟫`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L74-L83
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L74-L83

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open DiscreteStability.StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}

theorem DiscreteStability.StepBound.norm_sq_le (h : StepBound P lo hi) (u : E) : ‖P u‖ ^ 2 ≤ hi * ⟪P u, u⟫ := by sorry
