-- Prove2me | Theorems.Thm_DiscreteStability_ascent
-- name    : DiscreteStability.ascent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:37:58.620905+00:00
-- url     : https://prove2.me/theorems/17e72960-42d4-457f-9259-9235c06183d8
-- title:
--   Discrete Stability: ascent
-- statement:
--   **Lemma 4.1 (one-step ascent).** Let `d = P (g x)`. If `∇f = g` is `L`-Lipschitz on a set `S`
--   containing the segment `{x + τ d : τ ∈ [0, t]}`, then for every `s ∈ [0, t]`,
--   `f x + s (1 - (s/2) L λₙ(P)) ⟪P g, g⟫ ≤ f (x + s d)`.
--   (The paper states it for `t = 1`; allowing `t ≤ 1` is used in the proof of Theorem 6.1.)
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L19-L75
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean#L19-L75

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem DiscreteStability.ascent {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
    (hP : StepBound P lo hi) (hL : 0 ≤ L) {x : E} {t : ℝ}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) t, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ∀ s ∈ Icc (0 : ℝ) t,
      f x + s * (1 - s / 2 * L * hi) * ⟪P (g x), g x⟫ ≤ f (x + s • P (g x)) := by sorry
