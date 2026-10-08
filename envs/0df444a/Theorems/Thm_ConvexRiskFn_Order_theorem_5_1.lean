-- Prove2me | Theorems.Thm_ConvexRiskFn_Order_theorem_5_1
-- name    : ConvexRiskFn.Order.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:30.938064+00:00
-- url     : https://prove2.me/theorems/95319c9a-13cc-4cc5-a4c7-927f7e0ee4d2
-- title:
--   Theorem 5.1, p. 446 — a distribution-invariant ρ is consistent with ⪰icx iff it satisfies (A2) and is risk averse
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space on which a uniform random variable exists, let $p\in[1,\infty)$ and $\mathcal X=\mathcal L_p(\Omega,\mathcal F,P)$. Let $\rho:\mathcal X\to\mathbb R$ be distribution invariant: $\rho(X_1)=\rho(X_2)$ whenever $P(X_1\le t)=P(X_2\le t)$ for all $t$. Then
--
--   $$\rho\ \text{is consistent with}\ \succeq_{\mathrm{icx}}\quad\Longleftrightarrow\quad \rho\ \text{satisfies (A2) and is risk averse.}$$
--
--   Here consistency means: for all $X_1,X_2\in\mathcal X$, if $\mathbb E[u(X_2)]\ge\mathbb E[u(X_1)]$ for every increasing convex $u$ for which the expectations exist, then $\rho(X_2)\ge\rho(X_1)$. (A2) means $X\le Y$ a.s. implies $\rho(X)\le\rho(Y)$. Risk aversion means $\rho(X)\ge\rho(\mathbb E[X\mid\mathcal G])$ for every $\sigma$-algebra $\mathcal G\subset\mathcal F$, every $X\in\mathcal X$ and every version of the conditional expectation.
--
--   The theorem characterizes, among law-invariant risk functions, exactly those that respect the increasing convex order, the counterpart of second-order stochastic dominance for costs; mean–risk models such as mean–semideviation and CVaR-based ones are special cases. No convexity of $\rho$ is assumed.
--
--   **Formalization Note** The existence of a uniform random variable and $\mathcal X=\mathcal L_p$, $p\in[1,\infty)$, are the standing assumptions of the rest of §5.2 (p. 445). Elements of $\mathcal X$ are functions with `MemLp X p P`; the order in (A2) is the almost-sure order of $\mathcal L_p$; the increasing convex order is the published `StochasticOrders_MonotoneConvex_IcxOrder`.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 446, Theorem 5.1 (with the standing assumptions of §5.2, p. 445, and Definitions 5.1, p. 443, and 5.2, p. 445)

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory

namespace ConvexRiskFn.Order

/-- Theorem 5.1, p. 446: under the standing assumptions of §5.2 (`𝒳 = ℒ_p(Ω, ℱ, P)`, `p ∈ [1, ∞)`,
a uniform random variable exists), a distribution-invariant risk function is consistent with the
increasing convex order iff it satisfies (A2) and is risk averse. -/
theorem theorem_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hU : ∃ U : Ω → ℝ, IsUniformRV P U)
    (ρ : (Ω → ℝ) → ℝ) (hρ : DistInvariant P p ρ) :
    ConsistentIcx P p ρ ↔ A2 P p ρ ∧ RiskAverse P p ρ := by sorry

end ConvexRiskFn.Order
