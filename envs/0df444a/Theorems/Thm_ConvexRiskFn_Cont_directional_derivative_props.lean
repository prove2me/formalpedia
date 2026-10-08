-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_directional_derivative_props
-- name    : ConvexRiskFn.Cont.directional_derivative_props
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:52.335585+00:00
-- url     : https://prove2.me/theorems/4984dac5-c8c5-4109-bfc3-6206b49dcf98
-- title:
--   §3.1, pp. 436–437 — at X̄ ∈ int(dom ρ) the directional derivative ρ′(X̄,·) is finite, positively homogeneous, convex, and ρ(X) ≥ ρ(X̄) + ρ′(X̄, X − X̄)
-- statement:
--   Let $\mathcal X$ be a real normed space and $\rho:\mathcal X\to\overline{\mathbb R}$ a proper function satisfying (A1) (convexity). Let $\bar X$ be an interior point of $\operatorname{dom}\rho$. Then for every $X\in\mathcal X$ the one-sided directional derivative
--   $$\rho'(\bar X,X):=\lim_{t\downarrow0}\frac{\rho(\bar X+tX)-\rho(\bar X)}{t}$$
--   exists as a real number, and the function $\delta(\cdot):=\rho'(\bar X,\cdot):\mathcal X\to\mathbb R$ satisfies:
--
--   1. $\delta$ is positively homogeneous: $\delta(tX)=t\,\delta(X)$ for all $t>0$;
--   2. $\delta$ is convex on $\mathcal X$;
--   3. $\rho(X)\ge\rho(\bar X)+\delta(X-\bar X)$ for every $X\in\mathcal X$.
--
--   This is the construction from which the paper obtains an algebraic subgradient at interior points of the domain.
--
--   **Formalization Note** The statement asserts the existence of a real-valued $\delta$ to which the difference quotients converge as $t\to0^+$, so $\delta$ is finite valued and is the directional derivative. The quotient is written with `EReal.toReal`; since $\bar X$ is interior to the domain and $\rho$ is proper, $\rho(\bar X+tX)$ is finite for all small $t>0$, so this agrees with the paper's quotient along the limit. The paper also states convexity of $\delta$ and the inequality for an arbitrary $\bar X$ (where $\delta$ may take infinite values); only the case $\bar X\in\operatorname{int}(\operatorname{dom}\rho)$, the one the paper's argument uses, is formalized.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), pp. 436–437, §3.1, paragraph beginning "Let us observe that ρ always possesses an algebraic subgradient" (the directional derivative δ(·) := ρ′(X̄, ·))

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem directional_derivative_props {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ) (Xbar : E)
    (hXbar : Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ)) :
    ∃ δ : E → ℝ,
      (∀ X : E, Tendsto (fun t : ℝ => ((ρ (Xbar + t • X)).toReal - (ρ Xbar).toReal) / t)
        (𝓝[>] 0) (𝓝 (δ X))) ∧
      (∀ X : E, ∀ t : ℝ, 0 < t → δ (t • X) = t * δ X) ∧
      ConvexOn ℝ Set.univ δ ∧
      (∀ X : E, ρ Xbar + ((δ (X - Xbar) : ℝ) : EReal) ≤ ρ X) := by sorry

end ConvexRiskFn.Cont
