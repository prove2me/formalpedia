-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_theorem_16
-- name    : ErrBoundCplx.Cplx.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:58.377905+00:00
-- url     : https://prove2.me/theorems/a32ee621-8e63-49fb-b38c-fd516c7b50a3
-- title:
--   Theorem 16 — subgradient descent sequences of convex KL functions converge, with f(x_k) ≤ ψ(α_k) and ‖x_k − x*‖ ≤ (b/a)α_k + √(ψ(α_{k−1})/a)
-- statement:
--   **Theorem (complexity of descent sequences for convex KL functions).** Let $H$ be a real Hilbert space and $f : H \to (-\infty, +\infty]$ a proper, lower semicontinuous, convex function with $\operatorname{argmin} f \neq \emptyset$ and $\min f = 0$. Let $0 < r_0 < \bar r$ and assume that $f$ has the KL property on $[0 < f < \bar r]$ with desingularizing function $\varphi \in \mathcal K(0, \bar r)$:
--   $$\varphi'(f(x))\,\|\partial^0 f(x)\| \ge 1 \qquad \text{whenever } 0 < f(x) < \bar r.$$
--   Put $\alpha_0 = \varphi(r_0)$ and $\psi = (\varphi|_{[0, r_0]})^{-1} : [0, \alpha_0] \to [0, r_0]$, and assume (A): $\psi'$ is Lipschitz continuous on $[0, \alpha_0]$ with constant $\ell > 0$ and $\psi'(0) = 0$.
--
--   Let $(x_k)_{k\in\mathbb N}$ be a subgradient descent sequence with constants $a, b > 0$ — for each $k \ge 1$, (H1) $f(x_k) + a\|x_k - x_{k-1}\|^2 \le f(x_{k-1})$ and (H2) some $\omega_k \in \partial f(x_k)$ has $\|\omega_k\| \le b\|x_k - x_{k-1}\|$ — with $f(x_0) = r_0$. Let
--   $$\zeta = \frac{\sqrt{1 + 2\ell a b^{-2}} - 1}{\ell}, \qquad \alpha_{k+1} = \operatorname{argmin}\left\{\psi(u) + \frac{1}{2\zeta}(u - \alpha_k)^2 : u \ge 0\right\} \ (k \ge 0),$$
--   the one-dimensional worst-case proximal sequence started at $\alpha_0$. Then $(x_k)$ converges strongly to some minimizer $x^*$ of $f$, and
--   $$f(x_k) \le \psi(\alpha_k) \quad \forall k \ge 0, \qquad \|x_k - x^*\| \le \frac{b}{a}\,\alpha_k + \sqrt{\frac{\psi(\alpha_{k-1})}{a}} \quad \forall k \ge 1.$$
--
--   The theorem reduces the complexity of any first-order method producing a subgradient descent sequence to that of an explicit one-dimensional proximal recursion determined by the desingularizing function: $(\alpha_k)$ is a majorizing sequence "à la Kantorovich" for both the values and the iterates.
--
--   **Formalization Note** $f$ is `EReal`-valued and proper lsc convex in the sense of the published `GammaZero`; $\partial f$ is its `subgrad`, and the KL inequality is required for every element of $\partial f(x)$ (equivalent to the least-norm form, with $\|\partial^0 f(x)\| = +\infty$ when $\partial f(x) = \emptyset$). $\psi$ is a real function given as data with $\psi(\varphi(s)) = s$ on $[0, r_0]$; $\psi'$ is its derivative within $[0, \alpha_0]$, and the argmin in (22) is taken over $[0, \alpha_0]$, the domain of $\psi$. $\alpha_0 = \varphi(r_0)$ and $\zeta$ are computed from the data, not chosen. The inequality $f(x_k) \le \psi(\alpha_k)$ is stated in `EReal`.
-- source:
--   arXiv:1510.08234v3, Theorem 16, p. 18, (24)–(25); setting of §4.2, p. 17, (A), (21), (22)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
import Definitions.Def_ErrBoundCplx_Cplx_WorstCase
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, Theorem 16, p. 18 (complexity of descent sequences for convex KL
functions). `f` proper lsc convex with `argmin f ≠ ∅`, `min f = 0`, KL on `[0 < f < r̄]` with
`φ ∈ K(0, r̄)`; `(x_k)` a subgradient descent sequence with constants `a, b > 0` and
`f(x₀) = r₀ ∈ (0, r̄)`; `α₀ = φ(r₀)`, `ψ = (φ|[0,r₀])⁻¹` satisfying (A) with constant `ℓ`;
`(α_k)` the worst-case proximal sequence (22) with `ζ` of (21). Then `x_k` converges strongly to
a minimizer `x*`, `f(x_k) ≤ ψ(α_k)` for all `k ≥ 0` (24), and
`‖x_k − x*‖ ≤ (b/a) α_k + √(ψ(α_{k−1})/a)` for all `k ≥ 1` (25). -/
theorem theorem_16 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) (hS : ProfileSetting φ ψ rbar r0 ℓ)
    (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (hx0 : f (x 0) = (r0 : EReal))
    (α : ℕ → ℝ) (hα : IsWorstCaseProxSeq ψ (φ r0) (zeta ℓ a b) α) :
    ∃ xstar : H, f xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      (∀ k, f (x k) ≤ ((ψ (α k) : ℝ) : EReal)) ∧
      ∀ k ≥ 1, ‖x k - xstar‖ ≤ b / a * α k + Real.sqrt (ψ (α (k - 1)) / a) := by sorry

end ErrBoundCplx.Cplx
