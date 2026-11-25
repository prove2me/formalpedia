-- Prove2me | Theorems.Thm_DiscreteStability_StepBound_inner_sq_le
-- name    : DiscreteStability.StepBound.inner_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:41.874616+00:00
-- url     : https://prove2.me/theorems/0413cde2-bc21-5a91-a2ad-402a232bbd91
-- title:
--   Step Bound: inner sq le
-- statement:
--   Cauchy–Schwarz for the semi-inner product `(u, v) ↦ ⟪P u, v⟫`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L53-L68
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L53-L68

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

theorem DiscreteStability.StepBound.inner_sq_le (h : StepBound P lo hi) (u v : E) :
    ⟪P u, v⟫ ^ 2 ≤ ⟪P u, u⟫ * ⟪P v, v⟫ := by sorry
