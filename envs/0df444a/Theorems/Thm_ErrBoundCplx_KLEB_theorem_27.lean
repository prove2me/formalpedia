-- Prove2me | Theorems.Thm_ErrBoundCplx_KLEB_theorem_27
-- name    : ErrBoundCplx.KLEB.theorem_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:01.081722+00:00
-- url     : https://prove2.me/theorems/6af78b84-8a39-4abd-806e-3d4e78efa18d
-- title:
--   Theorem 27 — the KL inequality on B(x̄, ρ) ∩ [0 < f < r₀] ⇔ length(χ_x, t, s) ≤ φ(f(χ_x(t))) − φ(f(χ_x(s))); then χ_x converges strongly
-- statement:
--   Let $H$ be a real Hilbert space and let $f : H \to (-\infty, +\infty]$ be proper, convex and lower semicontinuous, with $\min f = 0$ and $S = \operatorname{argmin} f$. Let $r_0 > 0$, $\bar x \in S$, $\rho > 0$, and let $\varphi \in \mathcal K(0, r_0)$: $\varphi : [0, r_0) \to \mathbb R$ is continuous on $[0, r_0)$, of class $C^1$ on $(0, r_0)$, concave, with $\varphi(0) = 0$ and $\varphi' > 0$ on $(0, r_0)$. For $x \in \overline{\operatorname{dom} f}$, $\chi_x$ denotes the subgradient curve issued from $x$. The following are equivalent:
--
--   1. for each $y \in B(\bar x, \rho)$ with $0 < f(y) < r_0$,
--   $$\varphi'(f(y))\,\|\partial^0 f(y)\| \ge 1;$$
--   2. for each $x \in B(\bar x, \rho)$ with $0 < f(x) \le r_0$ and all $0 \le t < s$,
--   $$\operatorname{length}(\chi_x, t, s) \le \varphi(f(\chi_x(t))) - \varphi(f(\chi_x(s))).$$
--
--   Moreover, under these conditions, for every $x \in B(\bar x, \rho)$ with $0 < f(x) \le r_0$, $\chi_x(t)$ converges strongly to a point of $S$ as $t \to \infty$.
--
--   The theorem converts the KL inequality, a pointwise condition on the subgradients, into a uniform bound on the length of the subgradient curves, and this bound is what gives the error bound of Theorem 5 (i).
--
--   **Formalization Note** Here $\|\partial^0 f(y)\| = +\infty$ when $\partial f(y) = \emptyset$, so condition 1 is written "$\varphi'(f(y))\,\|v\| \ge 1$ for every $v \in \partial f(y)$". The ball is the open ball. Condition 2 quantifies over every subgradient curve issued from $x$ (by Theorem 1 there is exactly one). The length is the $[0, +\infty]$-valued integral of `ErrBoundCplx.KLEB.Setting`, and the right-hand side enters through `ENNReal.ofReal`. Since $\varphi$ is only defined on $[0, r_0)$, $\varphi(f(\chi_x(t)))$ has no meaning on the page when $f(\chi_x(t)) = r_0$ (possible only for $t = 0$ and $f(x) = r_0$); condition 2 is required whenever $f(\chi_x(t)) < r_0$. $K(0, r_0)$ is the published `IsDesingularizer r0 φ`, and $\varphi'$ is `deriv φ`.
-- source:
--   arXiv:1510.08234v3, Theorem 27, p. 25 (with the definition of χx and length(χx, t, s) on p. 25)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_KLEB_Setting
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open MoreauProx.Characterization NonconvexSplitting.ADMMKL Filter Topology

namespace ErrBoundCplx.KLEB

/-- Theorem 27, p. 25: for `x̄ ∈ S`, `ρ > 0` and `φ ∈ K(0, r₀)`, the KL inequality
`φ'(f(y)) ‖∂⁰f(y)‖ ≥ 1` on `B(x̄, ρ) ∩ [0 < f < r₀]` is equivalent to the length bound
`length(χ_x, t, s) ≤ φ(f(χ_x(t))) − φ(f(χ_x(s)))` for every `x ∈ B(x̄, ρ) ∩ [0 < f ≤ r₀]` and
`0 ≤ t < s` (whenever `f(χ_x(t)) < r₀`, i.e. `φ(f(χ_x(t)))` is defined); moreover, under these
conditions every such curve converges strongly to a minimizer. -/
theorem theorem_27 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (hmin : MinIsZero f)
    (r0 : ℝ) (hr0 : 0 < r0) (xbar : H) (hxbar : xbar ∈ argminSet f) (ρ : ℝ) (hρ : 0 < ρ)
    (φ : ℝ → ℝ) (hφ : IsDesingularizer r0 φ) :
    ((∀ y ∈ Metric.ball xbar ρ, 0 < f y → f y < (r0 : EReal) →
        ∀ v ∈ subgrad f y, 1 ≤ deriv φ (f y).toReal * ‖v‖) ↔
      (∀ x ∈ Metric.ball xbar ρ, 0 < f x → f x ≤ (r0 : EReal) →
        ∀ χ : ℝ → H, IsSubgradCurve f x χ →
          ∀ t s : ℝ, 0 ≤ t → t < s → f (χ t) < (r0 : EReal) →
            curveLength χ t s ≤ ENNReal.ofReal (φ (f (χ t)).toReal - φ (f (χ s)).toReal))) ∧
    ((∀ y ∈ Metric.ball xbar ρ, 0 < f y → f y < (r0 : EReal) →
        ∀ v ∈ subgrad f y, 1 ≤ deriv φ (f y).toReal * ‖v‖) →
      ∀ x ∈ Metric.ball xbar ρ, 0 < f x → f x ≤ (r0 : EReal) →
        ∀ χ : ℝ → H, IsSubgradCurve f x χ →
          ∃ xstar ∈ argminSet f, Tendsto χ atTop (𝓝 xstar)) := by sorry

end ErrBoundCplx.KLEB
