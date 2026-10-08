-- Prove2me | Theorems.Thm_ConvexOptAlg_CenterGravity_eq_2_2
-- name    : ConvexOptAlg.CenterGravity.eq_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:23:46.571979+00:00
-- url     : https://prove2.me/theorems/01fb94fb-fe3c-487c-a8a6-3e84751d978e
-- title:
--   Eq. (2.2), p. 246 — the cut of the center of gravity method removes only points where f exceeds f(c_t), so x* ∈ S_t
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a convex body and $f:\mathcal X\to[-B,B]$ continuous and convex, and let $x^*\in\mathcal X$ satisfy $f(x^*)=\min_{x\in\mathcal X}f(x)$. Let $(\mathcal S_t,c_t,w_t)_{t\ge1}$ be a run of the center of gravity method on $\mathcal X$ for $f$. Then for every $t\ge1$,
--   $$\mathcal S_t\setminus\mathcal S_{t+1}\subset\{x\in\mathcal X:(x-c_t)^\top w_t>0\}\subset\{x\in\mathcal X: f(x)>f(c_t)\},$$
--   and the optimal point is never removed:
--   $$x^*\in\mathcal S_t .$$
--
--   This is display (2.2) in the proof of Theorem 2.1 together with the consequence drawn from it in the next sentence. It says that each cut discards only points that are strictly worse than the point just queried.
--
--   **Formalization Note** The standing assumptions of Chapter 2 (convex body, continuity, convexity and the bound $|f|\le B$ on $\mathcal X$) and the existence of the minimizer $x^*$ (the book's standing notation, p. 242) are hypotheses. Subgradients are relative to $\mathcal X$ (Definition 1.2).
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, Eq. (2.2) and the sentence following it, p. 246

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, display (2.2) and the sentence after it, p. 246.
For a run `(S, c, w)` of the center of gravity method on the convex body `X` for a continuous convex
`f : X → [-B, B]` with minimizer `x*`, and every `t ≥ 1`:
`S_t \ S_{t+1} ⊂ {x ∈ X : (x - c_t)ᵀ w_t > 0} ⊂ {x ∈ X : f(x) > f(c_t)}` (2.2), and `x* ∈ S_t`. -/
theorem eq_2_2 {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    {S : ℕ → Set (EuclideanSpace ℝ (Fin n))} {c w : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : IsCenterOfGravityRun X f S c w) (t : ℕ) (ht : 1 ≤ t) :
    (S t \ S (t + 1) ⊆ {x | x ∈ X ∧ 0 < ⟪x - c t, w t⟫_ℝ} ∧
      {x | x ∈ X ∧ 0 < ⟪x - c t, w t⟫_ℝ} ⊆ {x | x ∈ X ∧ f (c t) < f x}) ∧
    xstar ∈ S t := by sorry

end ConvexOptAlg.CenterGravity
