-- Prove2me | Theorems.Thm_DiscreteStability_step_mono
-- name    : DiscreteStability.step_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:42:56.18482+00:00
-- url     : https://prove2.me/theorems/1228a44d-5007-5cb9-9446-691c3e3cd8e3
-- title:
--   Discrete Stability: step mono
-- statement:
--   **(C1)** Under S1, `V(x_{k+1}) ≤ V(x_k)`, i.e. `f x ≤ f (x + P g x)`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L110-L115
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L110-L115

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}

theorem DiscreteStability.step_mono (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x ≤ f (x + P (g x)) := by sorry
