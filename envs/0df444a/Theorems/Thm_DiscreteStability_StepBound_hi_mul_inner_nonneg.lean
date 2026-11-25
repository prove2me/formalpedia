-- Prove2me | Theorems.Thm_DiscreteStability_StepBound_hi_mul_inner_nonneg
-- name    : DiscreteStability.StepBound.hi_mul_inner_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:44.742797+00:00
-- url     : https://prove2.me/theorems/f191f4cc-be7e-524d-810a-46906ce3326a
-- title:
--   Step Bound: hi mul inner nonneg
-- statement:
--   The Step Bound construction uses the hi mul inner nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L70-L71
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L70-L71

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

theorem DiscreteStability.StepBound.hi_mul_inner_nonneg (h : StepBound P lo hi) (u : E) : 0 ≤ hi * ⟪P u, u⟫ := by sorry
