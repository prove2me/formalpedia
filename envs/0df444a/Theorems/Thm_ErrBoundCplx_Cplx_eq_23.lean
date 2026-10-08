-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_eq_23
-- name    : ErrBoundCplx.Cplx.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:31.801981+00:00
-- url     : https://prove2.me/theorems/0d109f4b-a2c3-4c24-b7d5-dcb52ccd46c1
-- title:
--   (23) — the worst-case proximal sequence exists, α_{k+1} = (I + ζψ′)⁻¹(α_k), α_k > 0 decreases to 0 and ψ(α_k) → 0
-- statement:
--   Let $\varphi \in \mathcal K(0, \bar r)$, $0 < r_0 < \bar r$, $\alpha_0 = \varphi(r_0)$ and $\psi = (\varphi|_{[0, r_0]})^{-1} : [0, \alpha_0] \to [0, r_0]$, and assume (A): $\psi$ is differentiable on $[0, \alpha_0]$, $\psi'$ is Lipschitz continuous on $[0, \alpha_0]$ with constant $\ell > 0$, and $\psi'(0) = 0$. Let $a, b > 0$ and
--   $$\zeta = \frac{\sqrt{1 + 2\ell a b^{-2}} - 1}{\ell}.$$
--   Then the one-dimensional worst-case proximal sequence
--   $$\alpha_{k+1} = \operatorname{argmin}\left\{\psi(u) + \frac{1}{2\zeta}(u - \alpha_k)^2 : u \in [0, \alpha_0]\right\}$$
--   started at $\alpha_0$ exists, and every such sequence satisfies, for all $k \ge 0$:
--   1. $\alpha_k > 0$;
--   2. $\alpha_{k+1} + \zeta\,\psi'(\alpha_{k+1}) = \alpha_k$, i.e. $\alpha_{k+1} = (I + \zeta\psi')^{-1}(\alpha_k) = \operatorname{prox}_{\zeta\psi}(\alpha_k)$;
--   3. $\alpha_{k+1} < \alpha_k$;
--
--   and moreover $\alpha_k \to 0$ and $\psi(\alpha_k) \to 0$ as $k \to \infty$.
--
--   These properties make $(\alpha_k)$ a well-defined majorizing sequence for Theorem 16; the existence part shows that the hypothesis "$(\alpha_k)$ is the worst-case proximal sequence" of Theorem 16 can always be met.
--
--   **Formalization Note** $\psi'$ is the derivative of $\psi$ within $[0, \alpha_0]$, and the minimization in (22) is over $[0, \alpha_0]$, the domain of $\psi$ (see the `WorstCase` definition module). "Decreasing" is stated as strict decrease, which is what the recursion gives for positive iterates.
-- source:
--   arXiv:1510.08234v3, §4.2, (21)–(23), pp. 17–18

import Mathlib
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_WorstCase
open NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, §4.2, (23), p. 18. In the setting of §4.2 (`φ ∈ K(0, r̄)`,
`0 < r₀ < r̄`, `ψ = (φ|[0,r₀])⁻¹`, (A) with constant `ℓ`) and with `ζ` given by (21) for
`a, b > 0`: the worst-case proximal sequence (22) exists; every such sequence is positive,
satisfies `α_{k+1} + ζ ψ'(α_{k+1}) = α_k` (that is `α_{k+1} = (I + ζψ')⁻¹(α_k)`), is strictly
decreasing, and `α_k → 0`, `ψ(α_k) → 0`. -/
theorem eq_23 (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) (hS : ProfileSetting φ ψ rbar r0 ℓ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ α : ℕ → ℝ, IsWorstCaseProxSeq ψ (φ r0) (zeta ℓ a b) α) ∧
      ∀ α : ℕ → ℝ, IsWorstCaseProxSeq ψ (φ r0) (zeta ℓ a b) α →
        (∀ k, 0 < α k) ∧
        (∀ k, α (k + 1) + zeta ℓ a b * psiPrime ψ (φ r0) (α (k + 1)) = α k) ∧
        (∀ k, α (k + 1) < α k) ∧
        Tendsto α atTop (𝓝 0) ∧
        Tendsto (fun k => ψ (α k)) atTop (𝓝 0) := by sorry

end ErrBoundCplx.Cplx
