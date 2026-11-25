-- Prove2me | Theorems.Thm_DiscreteStability_exists_pos_lower_bound
-- name    : DiscreteStability.exists_pos_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:32:31.527394+00:00
-- url     : https://prove2.me/theorems/45002d96-3b38-5387-85b4-2077765787c0
-- title:
--   Discrete Stability: exists pos lower bound
-- statement:
--   A continuous positive function on a compact set has a positive lower bound.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L112-L118
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean#L112-L118

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic
set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem DiscreteStability.exists_pos_lower_bound {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {φ : X → ℝ} (hc : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ φ x := by sorry
