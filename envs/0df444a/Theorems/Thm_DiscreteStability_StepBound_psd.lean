-- Prove2me | Theorems.Thm_DiscreteStability_StepBound_psd
-- name    : DiscreteStability.StepBound.psd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:31.70312+00:00
-- url     : https://prove2.me/theorems/38c3af28-8cae-4c18-9fbf-510a03980cd3
-- title:
--   Step Bound: psd
-- statement:
--   `P` is positive semidefinite.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L49-L50
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L49-L50

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

theorem DiscreteStability.StepBound.psd (h : StepBound P lo hi) (u : E) : 0 ≤ ⟪P u, u⟫ := by sorry
