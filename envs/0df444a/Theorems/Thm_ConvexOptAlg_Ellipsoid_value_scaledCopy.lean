-- Prove2me | Theorems.Thm_ConvexOptAlg_Ellipsoid_value_scaledCopy
-- name    : ConvexOptAlg.Ellipsoid.value_scaledCopy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:31:48.568891+00:00
-- url     : https://prove2.me/theorems/6c881216-0de1-4676-b210-095fe4ea4e1c
-- title:
--   §2.1, proof of Theorem 2.1, p. 247 — by convexity f(x_ε) ≤ f(x*) + 2εB on X_ε
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a convex body, $f$ continuous and convex on $\mathcal X$ with $-B\le f(x)\le B$ for $x\in\mathcal X$, $x^*\in\mathcal X$ a minimizer, and $\varepsilon\in[0,1]$. Then every point $x_\varepsilon$ of $\mathcal X_\varepsilon=\{(1-\varepsilon)x^*+\varepsilon x: x\in\mathcal X\}$ satisfies
--
--   $$
--   f(x_\varepsilon)\le f(x^*)+2\varepsilon B.
--   $$
--
--   Thus every point of the scaled copy is $2\varepsilon B$-optimal, which converts the volume argument into the value bound of Theorems 2.1 and 2.4.
--
--   **Formalization Note** The convex-body, continuity, and minimizer hypotheses follow the chapter setting and the proof of Theorem 2.1.
-- source:
--   Bubeck, arXiv:1405.4980v2, §2.1, proof of Theorem 2.1, p. 247

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

/-- Bubeck, arXiv:1405.4980v2, §2.1, proof of Theorem 2.1, p. 247: for a convex body `X`,
a continuous convex `f` on `X` with values in `[−B, B]`, its minimizer `x∗`, and `ε ∈ [0, 1]`, every
`x_ε ∈ X_ε = {(1 − ε)x∗ + εx : x ∈ X}` satisfies `f(x_ε) ≤ f(x∗) + 2εB`. -/
theorem value_scaledCopy {n : ℕ} (X : Set (Fin n → ℝ)) (hX : IsConvexBody X)
    (f : (Fin n → ℝ) → ℝ) (hfcont : ContinuousOn f X) (hf : ConvexOn ℝ X f)
    (B : ℝ) (hfB : ∀ x ∈ X, -B ≤ f x ∧ f x ≤ B)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (xε : Fin n → ℝ) (hxε : xε ∈ scaledCopy X xstar ε) :
    f xε ≤ f xstar + 2 * ε * B := by sorry

end ConvexOptAlg.Ellipsoid
