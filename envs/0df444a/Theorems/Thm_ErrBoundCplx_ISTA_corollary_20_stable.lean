-- Prove2me | Theorems.Thm_ErrBoundCplx_ISTA_corollary_20_stable
-- name    : ErrBoundCplx.ISTA.corollary_20_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:39.424526+00:00
-- url     : https://prove2.me/theorems/88d02f4f-536f-4d02-abb3-a202915b8ae2
-- title:
--   Corollary 20 with Corollary 19 — for ψ(s) = (ℓ/2)s² on a stable set, f(x_k) ≤ f(x₀)/(1 + 2aσ)^k and the bound (30), σ = ℓb⁻²
-- statement:
--   Let $H$ be a real Hilbert space and $f : H \to (-\infty, +\infty]$ proper, lower semicontinuous and convex, with $\operatorname{argmin} f \neq \emptyset$ and $\min f = 0$. Let $(x_k)$ be a subgradient descent sequence for $f$ with constants $a, b > 0$ and $f(x_0) = r_0 \in (0, \bar r)$. Let $X \subseteq H$ contain every $x_k$, let $\ell > 0$, and suppose $f$ has the KL property on $X \cap [0 < f < \bar r]$ with $\psi(s) = \frac{\ell}{2}s^2$, that is, with desingularizing function $\varphi(s) = \sqrt{2s/\ell}$:
--   $$\varphi'(f(x))\,\|v\| \ge 1 \qquad \text{for all } x \in X \text{ with } 0 < f(x) < \bar r \text{ and all } v \in \partial f(x).$$
--   Set $\sigma = \ell b^{-2}$ (28). Then $(x_k)$ converges strongly to some minimizer $x^*$ of $f$, and
--   $$f(x_k) \le \frac{f(x_0)}{(1 + 2a\sigma)^k} \qquad \forall k \ge 0, \qquad (29)$$
--   $$\|x_k - x^*\| \le \left[1 + \frac{1}{a\sigma\sqrt{1 + \frac{1}{2a\sigma}}}\right] \frac{\sqrt{\frac1a f(x_0)}}{(1 + 2a\sigma)^{\frac{k-1}{2}}} \qquad \forall k \ge 1. \qquad (30)$$
--
--   With $X = H$ this is Corollary 20, the quadratic-growth instance of the complexity Theorem 16; general $X$ is the stable-set version of Corollary 19, which is what the analysis of ISTA needs, since the KL inequality is only known on an $\ell_1$ ball.
--
--   **Formalization Note** $f$ takes values in `EReal`. The stability condition is $x_k \in X$ for all $k$; the page's "$x_k \in X \cap [0 < f < \bar r]$ for all $k$" is relaxed so that a sequence reaching $\operatorname{argmin} f$ in finite time is covered (the KL inequality is only used at points of the band). Theorem 16's assumption (A), the profile $\psi$ and the one-dimensional sequence are not carried: for $\psi(s) = \frac\ell2 s^2$, (A) holds automatically and the bounds are in closed form. $\varphi \in \mathcal K(0, \bar r)$ holds for this $\varphi$ and is not assumed. The definitions restate mission 01's locally.
-- source:
--   arXiv:1510.08234v3, Corollary 20, p. 20, (28)–(30), with Corollary 19, p. 19, and the assumptions of Theorem 16, p. 18

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_ISTA_DescentSeq
open MoreauProx.Characterization
open Filter Topology

namespace ErrBoundCplx.ISTA

/-- arXiv:1510.08234v3, Corollary 20 under the stable-set relaxation of Corollary 19,
pp. 19–20. Let `f : H → (−∞, +∞]` be proper lsc convex with `argmin f ≠ ∅` and `min f = 0`,
`(x_k)` a subgradient descent sequence with constants `a, b > 0` and `f(x₀) = r₀ ∈ (0, r̄)`,
`X ⊆ H` with `x_k ∈ X` for all `k`, and suppose `f` has the KL property on `X ∩ [0 < f < r̄]`
with `ψ(s) = (ℓ/2)s²`, i.e. with desingularizing function `φ(s) = √(2s/ℓ)`, `ℓ > 0`. With
`σ = ℓ b⁻²` (28), `x_k` converges strongly to a minimizer `x*` and
`f(x_k) ≤ f(x₀)/(1 + 2aσ)^k` for `k ≥ 0` (29),
`‖x_k − x*‖ ≤ [1 + 1/(aσ√(1 + 1/(2aσ)))] √(f(x₀)/a) / (1 + 2aσ)^((k−1)/2)` for `k ≥ 1` (30). -/
theorem corollary_20_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (hmin : ErrBoundCplx.Cplx.IsMinZero f)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (rbar r0 : ℝ) (hr0 : 0 < r0) (hr0bar : r0 < rbar)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (hx0 : f (x 0) = (r0 : EReal))
    (X : Set H) (hX : ∀ k, x k ∈ X)
    (hKL : KLOnSet f X rbar (fun s => Real.sqrt (2 * s / ℓ))) :
    let σ : ℝ := ℓ * b⁻¹ ^ 2
    ∃ xstar : H, f xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      (∀ k : ℕ, f (x k) ≤ ((r0 / (1 + 2 * a * σ) ^ k : ℝ) : EReal)) ∧
      ∀ k : ℕ, 1 ≤ k → ‖x k - xstar‖ ≤
        (1 + 1 / (a * σ * Real.sqrt (1 + 1 / (2 * a * σ)))) * Real.sqrt (1 / a * r0) /
          (1 + 2 * a * σ) ^ (((k : ℝ) - 1) / 2) := by sorry

end ErrBoundCplx.ISTA
