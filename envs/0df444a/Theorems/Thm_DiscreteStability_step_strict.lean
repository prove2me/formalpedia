-- Prove2me | Theorems.Thm_DiscreteStability_step_strict
-- name    : DiscreteStability.step_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:38:13.392803+00:00
-- url     : https://prove2.me/theorems/8c6a495d-cef2-5a7d-885c-24f2fe370f78
-- title:
--   Discrete Stability: step strict
-- statement:
--   **(C2)** Under S2 (`L λₙ(P) ≤ 2 - η`),
--   `V(x_{k+1}) ≤ V(x_k) - (η/2) λ₁(P) ‖∇f(x_k)‖²`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L131-L141
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L131-L141

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}

theorem DiscreteStability.step_strict (hP : StepBound P lo hi) (hL : 0 ≤ L) {η : ℝ} (hS2 : L * hi ≤ 2 - η)
    (hη : 0 ≤ η) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + η / 2 * lo * ‖g x‖ ^ 2 ≤ f (x + P (g x)) := by sorry
