-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_Supplement_lemma_8
-- name    : CubicNewton.Nonconvex.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:07:46.204514+00:00
-- url     : https://prove2.me/theorems/879824ec-2a0b-444d-ab15-345bf6b861fd
-- title:
--   Lemma 8 — $\|x-y\|\le\sigma\|u(x)-u(y)\|$ on $\mathcal L(f(x_0))$
-- statement:
--   In the setting of Section 4.3, let $f=\phi\circ u$ with $u$ invertible, $v=u^{-1}$, $\phi$ convex with bounded level sets, and let $\sigma$ bound $\|v'(z)\|$ on $S=\{z:\phi(z)\le f(x_0)\}$. Then for any $x,y\in\mathcal L(f(x_0))$
--   $$\|x-y\|\le\sigma\,\|u(x)-u(y)\| .\qquad(4.18)$$
--   The points $x,y$ need not be joined by a segment inside $\mathcal L(f(x_0))$; the transformed segment between $u(x)$ and $u(y)$ lies in the convex set $S$. The bound transfers distances from the transformed coordinates, where $\phi$ is convex, back to the original ones, and is used in Theorems 8 and 9.
--
--   Differences from the source:
--   - generalization: Section 4.3 non-degenerate u with differentiable inverse v; σ = max ‖v′(z)‖ and D = max ‖z − u*‖ on S → mutually inverse maps; v differentiable only on S; no derivative premise for u; σ and D arbitrary upper bounds on S; reason: the source hypotheses imply these fields, and all estimates use only the inverse derivative on the convex transformed sublevel set; choosing the printed maxima recovers the complete source claim
--   - generalization: stated under the paper's standing assumptions of Section 2 → only the Section 4.3 setting is assumed; reason: the Section 2 assumptions are not used by the statement; the Lean statement applies to every instance of the paper's
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 195, Lemma 8, (4.18)

import Mathlib
import Definitions.Def_CubicNewton_Nonconvex_Supplement_TransformedConvexSetting

namespace CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Lemma 8, (4.18), p. 195. In the setting of Section 4.3
(`f = φ ∘ u`, `v` the inverse of `u`, `σ` a bound on `‖v′‖` over `{z : φ(z) ≤ f(x₀)}`),
for any `x, y ∈ L(f(x₀))` we have `‖x − y‖ ≤ σ ‖u(x) − u(y)‖`. -/
theorem lemma_8 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (u v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (v' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ustar : EuclideanSpace ℝ (Fin n)) (σ D : ℝ)
    (hT : TransformedConvexSetting f x₀ φ u v v' ustar σ D) :
    ∀ x y : EuclideanSpace ℝ (Fin n), f x ≤ f x₀ → f y ≤ f x₀ →
      ‖x - y‖ ≤ σ * ‖u x - u y‖ := by sorry

end CubicNewton.Nonconvex.Supplement
