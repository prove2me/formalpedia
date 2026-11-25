-- Prove2me | Theorems.Thm_DiscreteStability_StepBound_norm_le
-- name    : DiscreteStability.StepBound.norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:32:47.760407+00:00
-- url     : https://prove2.me/theorems/eb2a1aca-d789-53c1-aaff-582b8f1e37cc
-- title:
--   Step Bound: norm le
-- statement:
--   Step-length bound: `‖P u‖ ≤ hi ‖u‖`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L86-L93
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L86-L93

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

theorem DiscreteStability.StepBound.norm_le (h : StepBound P lo hi) (u : E) : ‖P u‖ ≤ hi * ‖u‖ := by sorry
