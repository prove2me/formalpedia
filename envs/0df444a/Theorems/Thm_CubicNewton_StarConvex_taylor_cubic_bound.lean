-- Prove2me | Theorems.Thm_CubicNewton_StarConvex_taylor_cubic_bound
-- name    : CubicNewton.StarConvex.taylor_cubic_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:23:42.338272+00:00
-- url     : https://prove2.me/theorems/55425480-37ea-4662-ab33-02f626689c05
-- title:
--   Lemma 1 (2.3): $|f(y)-f(x)-\langle f'(x),y-x\rangle-\tfrac12\langle f''(x)(y-x),y-x\rangle|\le\tfrac L6\|y-x\|^3$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$ with gradient $f'$ and Hessian $f''$. Assume the Hessian is Lipschitz continuous on $F$ with constant $L > 0$ (Assumption 1):
--
--   $$\|f''(x) - f''(y)\| \le L\|x - y\| \quad \text{for all } x, y \in F,$$
--
--   where $\|\cdot\|$ on matrices is the spectral norm. Then for any $x$ and $y$ in $F$,
--
--   $$\Big| f(y) - f(x) - \langle f'(x), y - x\rangle - \tfrac12 \langle f''(x)(y - x), y - x\rangle \Big| \le \frac{L}{6}\,\|y - x\|^3 .$$
--
--   This is the cubic accuracy of the second-order Taylor model under a Lipschitz Hessian. Its lower half is what makes the cubic model with $M \ge L$ an upper bound for $f$, and it drives the per-step estimate in the $O(1/k^2)$ rate on star-convex functions.
--
--   **Formalization Note** The gradient and Hessian are maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every $x \in F$ (two-sided derivatives, also at boundary points of $F$). The Lipschitz condition uses the operator norm on `E →L[ℝ] E`, which is the spectral norm.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 181, Lemma 1, inequality (2.3)

import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.StarConvex

/-- Nesterov–Polyak 2006, Lemma 1, inequality (2.3), p. 181: under the standing assumptions of
Section 2 (F closed, convex, with nonempty interior; f twice differentiable on F with gradient `g`
and Hessian `H`; Assumption 1, the Hessian is `L`-Lipschitz on F), for any `x, y ∈ F`,
`|f(y) − f(x) − ⟨f′(x), y − x⟩ − ½⟨f″(x)(y − x), y − x⟩| ≤ (L/6)‖y − x‖³`. -/
theorem taylor_cubic_bound {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F,
      |f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫| ≤ L / 6 * ‖y - x‖ ^ 3 := by sorry

end CubicNewton.StarConvex
