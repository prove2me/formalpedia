-- Prove2me | Theorems.Thm_ConvexOptAlg_CoordDescent_thm_6_8_contraction
-- name    : ConvexOptAlg.CoordDescent.thm_6_8_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:09:01.489245+00:00
-- url     : https://prove2.me/theorems/d265d9f8-80bb-4c8a-aceb-4742aab3c060
-- title:
--   §6.4.2, proof of Theorem 6.8, pp. 341–342 — one RCD(γ) step contracts the expected gap by 1 − 1/κ_γ
-- statement:
--   Let $n\ge1$, $\gamma\ge0$, $\alpha>0$, $\beta_1,\dots,\beta_n>0$. Let $f:\mathbb R^n\to\mathbb R$ be differentiable, $\alpha$-strongly convex w.r.t. $\|\cdot\|_{[1-\gamma]}$, and directionally smooth with constants $\beta_i$, and let $x^*$ minimize $f$. Let $\kappa_\gamma=\sum_i\beta_i^\gamma/\alpha$. Then for every $x\in\mathbb R^n$,
--
--   $$\sum_{i=1}^n p_\gamma(i)\,f\Big(x-\frac{1}{\beta_i}\nabla_i f(x)e_i\Big)-f(x^*)\le\Big(1-\frac{1}{\kappa_\gamma}\Big)\big(f(x)-f(x^*)\big).$$
--
--   The left side is $\mathbb E_{i_s}f(x_{s+1})-f(x^*)$ given $x_s=x$. This combines the expected decrease of one step with Lemma 6.9 in the weighted norm; it is the pointwise inequality behind the "straightforward calculations" that end the proof of Theorem 6.8.
--
--   **Formalization Note** $n\ge1$, $\alpha>0$, $\beta_i>0$ are added for $p_\gamma$, $\kappa_\gamma$ and the step. The minimizer is the book's standing assumption.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.4.2, proof of Theorem 6.8, pp. 341–342

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace ConvexOptAlg.CoordDescent

/-- Proof of Theorem 6.8, the contraction behind "straightforward calculations" (Bubeck,
arXiv:1405.4980v2, pp. 341–342): under the hypotheses of Theorem 6.8, for every point `x` (the current
iterate `x_s`), one RCD(γ) step with the coordinate drawn from `p_γ` satisfies
`Σᵢ p_γ(i) f(x − (1/βᵢ)∇ᵢ f(x) eᵢ) − f(x*) ≤ (1 − 1/κ_γ)(f(x) − f(x*))`, `κ_γ = Σᵢ βᵢ^γ / α`. -/
theorem thm_6_8_contraction {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ α : ℝ)
    (hγ : 0 ≤ γ) (hβ : ∀ i, 0 < β i) (hα : 0 < α)
    (hsc : IsStronglyConvexWNorm f g β (1 - γ) α) (hsm : IsCoordSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, pGamma β γ i * f (rcdStep β g x i)) - f xstar ≤
      (1 - 1 / kappa β γ α) * (f x - f xstar) := by sorry

end ConvexOptAlg.CoordDescent
