-- Prove2me | Theorems.Thm_ConvexOptAlg_CenterGravity_thm_2_1_value_scaled_copy
-- name    : ConvexOptAlg.CenterGravity.thm_2_1_value_scaled_copy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:24:16.949415+00:00
-- url     : https://prove2.me/theorems/d99426e6-a194-4cc9-9dd0-a7b38af58399
-- title:
--   Proof of Theorem 2.1, p. 247 — every x_ε = (1 − ε)x* + εx ∈ X_ε satisfies f(x_ε) ≤ f(x*) + 2εB
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a convex body, $f:\mathcal X\to[-B,B]$ continuous and convex, $x^*\in\mathcal X$ a minimizer of $f$ on $\mathcal X$, and $\varepsilon\in[0,1]$. For every $x\in\mathcal X$ the point $x_\varepsilon=(1-\varepsilon)x^*+\varepsilon x$ of $\mathcal X_\varepsilon$ satisfies
--   $$f(x_\varepsilon)\le f(x^*)+2\varepsilon B .$$
--
--   Points of the shrunk copy $\mathcal X_\varepsilon$ are $2\varepsilon B$-optimal; this is the last inequality of the proof of Theorem 2.1.
--
--   **Formalization Note** $|f|\le B$ is required on $\mathcal X$ only; values of $f$ outside $\mathcal X$ play no role. The standing assumptions of Chapter 2 are hypotheses.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, p. 247

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, p. 247: for `ε ∈ [0, 1]` and every point
`x_ε = (1 - ε)x* + εx` of `X_ε` (`x ∈ X`), convexity of `f` gives `f(x_ε) ≤ f(x*) + 2εB`. Standing
assumptions of Ch. 2: `X` a convex body, `f : X → [-B, B]` continuous and convex, `x*` a minimizer. -/
theorem thm_2_1_value_scaled_copy {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) :
    f ((1 - ε) • xstar + ε • x) ≤ f xstar + 2 * ε * B := by sorry

end ConvexOptAlg.CenterGravity
