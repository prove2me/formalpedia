-- Prove2me | Theorems.Thm_DiscreteStability_step_weighted
-- name    : DiscreteStability.step_weighted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:38:11.567522+00:00
-- url     : https://prove2.me/theorems/c47e1e15-af39-464f-8f57-4a5223e05120
-- title:
--   Discrete Stability: step weighted
-- statement:
--   Weighted decrease: `f x + ½ λ₁(P) (2 - L λₙ(P)) ‖g x‖² ≤ f (x + P g x)` under S1.
--   This is the inequality used in Corollary 5.2.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L119-L127
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L119-L127

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}

theorem DiscreteStability.step_weighted (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + lo * (2 - L * hi) / 2 * ‖g x‖ ^ 2 ≤ f (x + P (g x)) := by sorry
