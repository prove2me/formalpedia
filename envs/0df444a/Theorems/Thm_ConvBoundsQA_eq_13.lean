-- Prove2me | Theorems.Thm_ConvBoundsQA_eq_13
-- name    : ConvBoundsQA.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:48.759989+00:00
-- url     : https://prove2.me/theorems/2e0d460b-9c2c-407a-83e5-d02321bd5bbd
-- title:
--   Display (13) — RVaR and quantiles of the tail distribution
-- statement:
--   Let $\mu$ be a Borel probability measure on $\mathbb R$ and $t\in[0,1)$, and let $\mu^{t+}$ be its $t$-tail distribution. Then
--   $$
--   R_{\beta,\alpha}(\mu^{t+})=R_{(1-t)\beta,(1-t)\alpha}(\mu)\quad\text{for all }0\le\beta<\beta+\alpha\le1,
--   $$
--   $$
--   q^-_u(\mu^{t+})=q^-_{t+(1-t)u}(\mu)\quad\text{for all }u\in(0,1].
--   $$
--
--   The tail distribution rescales the quantile levels $[t,1]$ of $\mu$ onto $[0,1]$; these identities are what reduce problems at level $t$ to level $0$ (Proposition 1).
--
--   **Formalization Note** RVaR values and quantiles are extended reals; Lean's $R$ is total.
--
--   Differences from the source:
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
--   - generalization: $R_{0,1}$ is defined only on $\mathcal M_1$, so at $t=0$, $(\beta,\alpha)=(0,1)$ the identity speaks of defined values → the identity for every probability measure, with $R_{0,1}=-\infty$ when the mean is undefined; reason: there $\mu^{0+}=\mu$ and both sides are the same value; for $t>0$ every term is defined
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, (13), p.10

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_R
import Definitions.Def_ConvBoundsQA_tailDist

open MeasureTheory

namespace ConvBoundsQA

/-- Display (13): for a probability measure `μ` on `ℝ` and `t ∈ [0, 1)`,
`R_{β,α}(μ^{t+}) = R_{(1−t)β,(1−t)α}(μ)` for all `0 ⩽ β < β + α ⩽ 1`, and
`q⁻_u(μ^{t+}) = q⁻_{t+(1−t)u}(μ)` for all `u ∈ (0, 1]`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5, (13), p.10).

**Formalization Note** `μ^{t+}` is `tailDist μ t`. `R` is total in Lean: at `(β, α) = (0, 1)` and
`t = 0` both sides are `R_{0,1}(μ)` (the mean, undefined outside `M₁`, where it takes the value `−∞`),
and the identity is stated for that value as well. -/
theorem eq_13 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∀ β α : ℝ, 0 ≤ β → β < β + α → β + α ≤ 1 →
        R β α (tailDist μ t) = R ((1 - t) * β) ((1 - t) * α) μ) ∧
      (∀ u ∈ Set.Ioc (0 : ℝ) 1, qMinus u (tailDist μ t) = qMinus (t + (1 - t) * u) μ) := by sorry

end ConvBoundsQA
