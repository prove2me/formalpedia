-- Prove2me | Theorems.Thm_ConvexRiskFn_Order_quantile_coupling
-- name    : ConvexRiskFn.Order.quantile_coupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:31.972008+00:00
-- url     : https://prove2.me/theorems/fec90404-43ce-4869-8f6d-3ca2e0e38d15
-- title:
--   Proof of Lemma 5.1, p. 446 — F_X⁻¹(U) has the law of X, and F_{X₂} ≤ F_{X₁} gives F_{X₁}⁻¹(U) ≤ F_{X₂}⁻¹(U)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a uniform random variable $U$ (measurable, $P(U\le t)=t$ for $t\in[0,1]$). For a random variable $X$ with cdf $F_X$, write $F_X^{-1}(t)=\inf\{s:F_X(s)\ge t\}$ and $\widehat X:=F_X^{-1}(U)$.
--
--   1. For every measurable $X$, $\widehat X$ is a random variable with the same distribution as $X$:
--   $$P\big(F_X^{-1}(U)\le t\big)=P(X\le t)\qquad\text{for all } t\in\mathbb R.$$
--   2. For measurable $X_1,X_2$ with $F_{X_2}(t)\le F_{X_1}(t)$ for all $t$,
--   $$F_{X_1}^{-1}(U)\ \le\ F_{X_2}^{-1}(U)\qquad\text{almost surely.}$$
--
--   This is the quantile construction of the proof of Lemma 5.1: it realizes two random variables ordered by $\succeq_{\mathrm{st}}$ as pointwise ordered random variables with the same laws on the same space.
--
--   **Formalization Note** The paper says "for all $\omega\in\Omega$". The Lean states the order almost surely: $U\in(0,1)$ only almost surely, and outside $(0,1)$ the paper's $F^{-1}$ is $\pm\infty$ while the Lean real infimum returns $0$.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 446, proof of Lemma 5.1, second paragraph

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory

namespace ConvexRiskFn.Order

/-- Proof of Lemma 5.1, p. 446: for a uniform random variable `U`, `X̂ := F_X⁻¹(U)` is a random
variable with the distribution of `X`, and `F_{X₂} ≤ F_{X₁}` gives `F_{X₁}⁻¹(U) ≤ F_{X₂}⁻¹(U)`
(almost surely: `U ∈ (0, 1)` only almost surely). -/
theorem quantile_coupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : IsUniformRV P U) :
    (∀ X : Ω → ℝ, Measurable X →
        Measurable (fun ω => cdfInv (cdfOf P X) (U ω)) ∧
        ∀ t : ℝ, P {ω | cdfInv (cdfOf P X) (U ω) ≤ t} = P {ω | X ω ≤ t}) ∧
    (∀ X₁ X₂ : Ω → ℝ, Measurable X₁ → Measurable X₂ →
        (∀ t : ℝ, cdfOf P X₂ t ≤ cdfOf P X₁ t) →
        ∀ᵐ ω ∂P, cdfInv (cdfOf P X₁) (U ω) ≤ cdfInv (cdfOf P X₂) (U ω)) := by sorry

end ConvexRiskFn.Order
