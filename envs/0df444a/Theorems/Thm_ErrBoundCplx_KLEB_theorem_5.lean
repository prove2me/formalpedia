-- Prove2me | Theorems.Thm_ErrBoundCplx_KLEB_theorem_5
-- name    : ErrBoundCplx.KLEB.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:48.485877+00:00
-- url     : https://prove2.me/theorems/4c623146-42e9-4121-9157-01566c73d1cb
-- title:
--   Theorem 5 — for convex f, the KL inequality gives dist(x, S) ≤ φ(f(x)), and with sφ′(s) ≥ cφ(s) that error bound gives φ′(f(x))‖∂⁰f(x)‖ ≥ c
-- statement:
--   This is the characterization of Łojasiewicz inequalities for convex functions.
--
--   Let $H$ be a real Hilbert space and let $f : H \to (-\infty, +\infty]$ be proper, convex and lower semicontinuous, with $\min f = 0$; write $S = \operatorname{argmin} f$ and $\operatorname{dist}(x, S) = \inf_{z \in S}\|x - z\|$. Let $r_0 > 0$, let $\varphi \in \mathcal K(0, r_0)$ (continuous on $[0, r_0)$, $C^1$ on $(0, r_0)$, concave, $\varphi(0) = 0$, $\varphi' > 0$), and let $c > 0$, $\rho > 0$ and $\bar x \in S$. For $x \in \operatorname{dom}\partial f$, $\partial^0 f(x)$ is the least-norm element of $\partial f(x)$, and $\|\partial^0 f(x)\| = +\infty$ when $\partial f(x) = \emptyset$.
--
--   1. **KL inequality implies error bound.** If $\varphi'(f(x))\,\|\partial^0 f(x)\| \ge 1$ for all $x \in [0 < f < r_0] \cap B(\bar x, \rho)$, then
--   $$\operatorname{dist}(x, S) \le \varphi(f(x)) \qquad \text{for all } x \in [0 < f < r_0] \cap B(\bar x, \rho).$$
--   2. **Error bound implies KL inequality.** Conversely, if $\varphi$ has a moderate behavior,
--   $$s\,\varphi'(s) \ge c\,\varphi(s) \qquad \text{for all } s \in (0, r_0),$$
--   and $\varphi(f(x)) \ge \operatorname{dist}(x, S)$ for all $x \in [0 < f < r_0] \cap B(\bar x, \rho)$, then
--   $$\varphi'(f(x))\,\|\partial^0 f(x)\| \ge c \qquad \text{for all } x \in [0 < f < r_0] \cap B(\bar x, \rho).$$
--
--   Here $[0 < f < r_0] = \{x \in H : 0 < f(x) < r_0\}$. Together, the two parts say that for desingularizing functions of moderate behavior the KL inequality and the error bound with residual function $\varphi$ are the same property, up to the constant $c$. Error bounds are often easier to establish than KL inequalities, and KL inequalities with explicit $\varphi$ are what yields complexity bounds for first-order methods.
--
--   **Formalization Note** "$\varphi'(f(x))\,\|\partial^0 f(x)\| \ge \kappa$" is written "$\varphi'(f(x))\,\|v\| \ge \kappa$ for every $v \in \partial f(x)$", which is the least-norm form with the convention $\|\partial^0 f(x)\| = +\infty$ off $\operatorname{dom}\partial f$. The ball $B(\bar x, \rho)$ is the open ball. $f$ takes values in `EReal`; on the band $f(x)$ is real and enters $\varphi$ and $\varphi' = $ `deriv φ` through `toReal`. $\operatorname{dist}(x, S)$ is `Metric.infDist x S`, with $S \ni \bar x$ nonempty. $\mathcal K(0, r_0)$ is the published `IsDesingularizer r0 φ`.
-- source:
--   arXiv:1510.08234v3, Theorem 5, p. 8

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_KLEB_Setting
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open MoreauProx.Characterization NonconvexSplitting.ADMMKL

namespace ErrBoundCplx.KLEB

/-- Theorem 5 (characterization of Łojasiewicz inequalities for convex functions), p. 8.
(i) The KL inequality `φ'(f(x)) ‖∂⁰f(x)‖ ≥ 1` on `[0 < f < r₀] ∩ B(x̄, ρ)` implies the error
bound `dist(x, S) ≤ φ(f(x))` there. (ii) If `φ` has a moderate behavior
`sφ'(s) ≥ cφ(s)` on `(0, r₀)`, the error bound on `[0 < f < r₀] ∩ B(x̄, ρ)` implies
`φ'(f(x)) ‖∂⁰f(x)‖ ≥ c` there. -/
theorem theorem_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (hmin : MinIsZero f)
    (r0 : ℝ) (hr0 : 0 < r0) (φ : ℝ → ℝ) (hφ : IsDesingularizer r0 φ)
    (c : ℝ) (hc : 0 < c) (ρ : ℝ) (hρ : 0 < ρ) (xbar : H) (hxbar : xbar ∈ argminSet f) :
    ((∀ x ∈ Metric.ball xbar ρ, 0 < f x → f x < (r0 : EReal) →
        ∀ v ∈ subgrad f x, 1 ≤ deriv φ (f x).toReal * ‖v‖) →
      ∀ x ∈ Metric.ball xbar ρ, 0 < f x → f x < (r0 : EReal) →
        Metric.infDist x (argminSet f) ≤ φ (f x).toReal) ∧
    ((∀ s ∈ Set.Ioo 0 r0, c * φ s ≤ s * deriv φ s) →
      (∀ x ∈ Metric.ball xbar ρ, 0 < f x → f x < (r0 : EReal) →
        Metric.infDist x (argminSet f) ≤ φ (f x).toReal) →
      ∀ x ∈ Metric.ball xbar ρ, 0 < f x → f x < (r0 : EReal) →
        ∀ v ∈ subgrad f x, c ≤ deriv φ (f x).toReal * ‖v‖) := by sorry

end ErrBoundCplx.KLEB
