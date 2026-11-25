-- Prove2me | Theorems.Thm_DiscreteStability_segment_ge
-- name    : DiscreteStability.segment_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:38:08.366708+00:00
-- url     : https://prove2.me/theorems/4a276756-5a81-4c68-95c6-8c1bffa49e3b
-- title:
--   Discrete Stability: segment ge
-- statement:
--   **(C3)** Under S1 (`L λₙ(P) ≤ 2`), `f` does not fall below `f x` anywhere along the step.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L93-L107
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L93-L107

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}

theorem DiscreteStability.segment_ge (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E} {t : ℝ}
    (ht : t ≤ 1)
    (hseg : ∀ τ ∈ Icc (0 : ℝ) t, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ∀ s ∈ Icc (0 : ℝ) t, f x ≤ f (x + s • P (g x)) := by sorry
