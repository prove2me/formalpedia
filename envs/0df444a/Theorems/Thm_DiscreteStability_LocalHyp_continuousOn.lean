-- Prove2me | Theorems.Thm_DiscreteStability_LocalHyp_continuousOn
-- name    : DiscreteStability.LocalHyp.continuousOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:43:01.068653+00:00
-- url     : https://prove2.me/theorems/f5fd01e4-a184-5129-b8bd-8c4ebd05d8b5
-- title:
--   Local Hyp: continuous On
-- statement:
--   The Local Hyp construction uses the continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L44-L45
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L44-L45

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}

theorem DiscreteStability.LocalHyp.continuousOn (hH : LocalHyp f g xbar r₀ L) : ContinuousOn f (closedBall xbar r₀) := by sorry
