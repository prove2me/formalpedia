-- Prove2me | Theorems.Thm_DNNProj_proposition_3
-- name    : DNNProj.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:31.532011+00:00
-- url     : https://prove2.me/theorems/10403a19-082b-4772-9318-7dc299f88c16
-- title:
--   Proposition 3 — $\partial\theta$ metrically subregular at $\bar x$ for $\bar v$ iff a local quadratic growth of $\theta$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $\theta:\mathcal H\to(-\infty,+\infty]$ a proper lower semicontinuous convex function, and let $(\bar x,\bar v)\in\operatorname{gph}\partial\theta$. Then $\partial\theta$ is metrically subregular at $\bar x$ for $\bar v$ (Definition 2, for some modulus) if and only if there are constants $\kappa>0$ and $\varepsilon>0$ with
--   $$\theta(x)\ge\theta(\bar x)+\langle\bar v,x-\bar x\rangle+\kappa\operatorname{dist}^2\big(x,(\partial\theta)^{-1}(\bar v)\big)\qquad\forall x\in\mathbb B_\varepsilon(\bar x).$$
--   This converts metric subregularity of a subdifferential into a growth inequality; the paper uses it for $\delta_{\mathcal Q}$, $\delta_{\mathbb N^n}$ and $\delta_{\mathbb S^n_+}$.
--
--   **Formalization Note** No finite dimensionality is assumed; $\theta(\bar x)$ is finite because $\partial\theta(\bar x)\ne\emptyset$.
--
--   Differences from the source:
--   - encoding: functions with values in (−∞, +∞] → EReal-valued functions; θ(x̄), p(x) at points where they are finite enter as real numbers (toReal); reason: Lean convention; the values are finite at every such point (the subdifferential there is nonempty), so no instance changes
--   - encoding: ∂f(x), the convex-analysis subdifferential → subdiff f x, empty where f x is not finite; reason: standard convention for proper functions; ∂f(x) = ∅ off dom f
--   - encoding: Definition 2 with dist(ȳ, F(x)), possibly over F(x) = ∅ → Metric.infEDist (values in [0, ∞]) on both sides, with modulus κ > 0 existentially quantified; reason: dist to the empty set is +∞ as the infimum over ∅; Metric.infDist would give 0 and change the property
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Proposition 3, p.7

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_DNNProj_Basics

open scoped RealInnerProductSpace

namespace DNNProj

/-- **Proposition 3** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.7; proved in [2, Theorem 3.3]).
Let `ℋ` be a real Hilbert space and `θ : ℋ → (−∞, +∞]` a proper lower semicontinuous convex
function, and let `(x̄, v̄) ∈ gph(∂θ)`. Then `∂θ` is metrically subregular at `x̄` for `v̄` if and
only if there are `κ > 0`, `ε > 0` with
`θ(x) ≥ θ(x̄) + ⟨v̄, x − x̄⟩ + κ dist²(x, (∂θ)⁻¹(v̄))` for all `x ∈ 𝔹_ε(x̄)`.

**Formalization Note.** `θ` takes values in `EReal`; "proper lower semicontinuous convex" is the
published `TensorAHPE.IsProperClosedConvex`; `θ(x̄)` is finite because `∂θ(x̄) ≠ ∅` and
enters as `(θ x̄).toReal`. "Metrically subregular" is Definition 2 for some modulus `κ > 0`
(`MetricSubregular`, with `infEDist`, so `dist(v̄, ∅) = +∞`). `(∂θ)⁻¹(v̄)` contains `x̄`, so
`Metric.infDist` to it is the true distance. No finite dimensionality is assumed. -/
theorem proposition_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (θ : H → EReal) (hθ : TensorAHPE.IsProperClosedConvex θ) (xbar vbar : H)
    (hgph : vbar ∈ subdiff θ xbar) :
    MetricSubregular (subdiff θ) xbar vbar ↔
      ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ∀ x ∈ Metric.closedBall xbar ε,
        ((((θ xbar).toReal + ⟪vbar, x - xbar⟫ +
            κ * Metric.infDist x (invMap (subdiff θ) vbar) ^ 2 : ℝ)) : EReal) ≤ θ x := by sorry

end DNNProj
