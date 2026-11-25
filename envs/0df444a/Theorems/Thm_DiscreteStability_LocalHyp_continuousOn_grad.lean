-- Prove2me | Theorems.Thm_DiscreteStability_LocalHyp_continuousOn_grad
-- name    : DiscreteStability.LocalHyp.continuousOn_grad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:43:39.704609+00:00
-- url     : https://prove2.me/theorems/81324c00-1f84-4ae8-bc8d-bd077077e0b3
-- title:
--   Local Hyp: continuous On grad
-- statement:
--   The Local Hyp construction uses the continuous On grad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L47-L49
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L47-L49

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}

theorem DiscreteStability.LocalHyp.continuousOn_grad (hH : LocalHyp f g xbar r₀ L) :
    ContinuousOn g (closedBall xbar r₀) := by sorry
