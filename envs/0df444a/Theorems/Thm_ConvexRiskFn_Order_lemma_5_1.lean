-- Prove2me | Theorems.Thm_ConvexRiskFn_Order_lemma_5_1
-- name    : ConvexRiskFn.Order.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:35.697993+00:00
-- url     : https://prove2.me/theorems/86ea931c-31c7-455a-b4f2-7cf139653c41
-- title:
--   Lemma 5.1, p. 445 — a distribution-invariant ρ is consistent with ⪰st iff it satisfies (A2)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space on which a uniform random variable exists, let $p\in[1,\infty)$ and $\mathcal X=\mathcal L_p(\Omega,\mathcal F,P)$. Let $\rho:\mathcal X\to\mathbb R$ be distribution invariant. Then
--
--   $$\rho \text{ is consistent with the usual stochastic order}\iff \rho \text{ satisfies (A2)},$$
--
--   where consistency means $X_2\succeq_{\mathrm{st}}X_1\Rightarrow\rho(X_2)\ge\rho(X_1)$ for $X_1,X_2\in\mathcal X$, and (A2) means $X\le Y$ almost surely $\Rightarrow\rho(X)\le\rho(Y)$.
--
--   The lemma is the first-order half of Theorem 5.1: it is used there to obtain (A2) from consistency with the increasing convex order.
--
--   **Formalization Note** The uniform random variable and $\mathcal X=\mathcal L_p$, $p\in[1,\infty)$, are the standing assumptions the paper places on the remainder of §5.2 (p. 445), immediately before the lemma.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 445, Lemma 5.1 (with the standing assumptions of §5.2, p. 445)

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory

namespace ConvexRiskFn.Order

/-- Lemma 5.1, p. 445: under the standing assumptions of §5.2 (`𝒳 = ℒ_p(Ω, ℱ, P)`, `p ∈ [1, ∞)`,
a uniform random variable exists), a distribution-invariant risk function is consistent with the
usual stochastic order iff it satisfies (A2). -/
theorem lemma_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hU : ∃ U : Ω → ℝ, IsUniformRV P U)
    (ρ : (Ω → ℝ) → ℝ) (hρ : DistInvariant P p ρ) :
    ConsistentSt P p ρ ↔ A2 P p ρ := by sorry

end ConvexRiskFn.Order
