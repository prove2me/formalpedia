-- Prove2me | Theorems.Thm_DiscreteStability_StepBound_hi_nonneg
-- name    : DiscreteStability.StepBound.hi_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:25.627515+00:00
-- url     : https://prove2.me/theorems/5e8ac343-20fa-52c7-8033-f274fffb6981
-- title:
--   Step Bound: hi nonneg
-- statement:
--   The Step Bound construction uses the hi nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L46-L46
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L46-L46

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

theorem DiscreteStability.StepBound.hi_nonneg (h : StepBound P lo hi) : 0 ≤ hi := by sorry
