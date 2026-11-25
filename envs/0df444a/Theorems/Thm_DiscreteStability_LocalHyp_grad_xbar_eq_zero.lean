-- Prove2me | Theorems.Thm_DiscreteStability_LocalHyp_grad_xbar_eq_zero
-- name    : DiscreteStability.LocalHyp.grad_xbar_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:44:01.535892+00:00
-- url     : https://prove2.me/theorems/09522a5d-5290-4fdf-8ad1-413a9a3c1fff
-- title:
--   Local Hyp: grad xbar eq zero
-- statement:
--   At an interior local maximum the gradient vanishes.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L52-L64
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L52-L64

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}

theorem DiscreteStability.LocalHyp.grad_xbar_eq_zero (hH : LocalHyp f g xbar r₀ L) (hH1 : IsolatedMax f xbar) :
    g xbar = 0 := by sorry
