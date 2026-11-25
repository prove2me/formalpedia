-- Prove2me | Theorems.Thm_DiscreteStability_ascent_step
-- name    : DiscreteStability.ascent_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:38:11.80813+00:00
-- url     : https://prove2.me/theorems/0d6fe763-2be9-5146-8a93-c6f47b515d98
-- title:
--   Discrete Stability: ascent step
-- statement:
--   The full step `[x, x + P g x]`, used with `t = 1`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L82-L90
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L82-L90

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}

theorem DiscreteStability.ascent_step (hP : StepBound P lo hi) (hL : 0 ≤ L) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + (1 - L * hi / 2) * ⟪P (g x), g x⟫ ≤ f (x + P (g x)) := by sorry
