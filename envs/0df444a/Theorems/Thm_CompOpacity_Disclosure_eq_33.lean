-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_eq_33
-- name    : CompOpacity.Disclosure.eq_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:37.604488+00:00
-- url     : https://prove2.me/theorems/b10c2cff-a26b-4f98-b257-150d1f077586
-- title:
--   (33), p. 33 — without competition, ∂Π^NC/∂m = (m + q − (1−a)(1−4a)n)/(2(1−a)²[q+m+(1−a)n]³) − c_m m
-- statement:
--   Without competition ($b = 0$), let $a \in [0, \tfrac12]$, $q, n, \bar\theta, c_m > 0$ and let the other FI's precision be $m_{-i} \ge 0$. Let $\Pi^{NC}_i(m_i)$ be FI $i$'s payoff (9), net of the disclosure cost $\tfrac{c_m}{2}m_i^2$, when investors play the linear equilibrium. Then at every $m_i > 0$,
--   $$\frac{\partial \Pi^{NC}_i}{\partial m_i} = \frac{m_i + q - (1-a)(1-4a)n}{2(1-a)^2[q + m_i + (1-a)n]^3} - c_m m_i.$$
--
--   The first term is the coordination benefit net of the volatility cost of disclosure; its sign at $m_i = 0$ decides whether the FI discloses at all (Proposition 2).
--
--   **Formalization Note** The derivative is that of the payoff computed as an expectation under the model's Gaussian law, with the investors' strategy given by the linear-equilibrium predicate, not of a closed-form expression.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 33, (31)–(33), proof of Proposition 2

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- (33), p. 33: without competition (`b = 0`), at every precision `t > 0` FI `i`'s equilibrium
payoff (9) net of the disclosure cost has derivative in its own precision
`∂Πᴺᶜᵢ/∂mᵢ = (mᵢ + q − (1 − a)(1 − 4a)n)/(2(1 − a)²[q + mᵢ + (1 − a)n]³) − c_m mᵢ`. -/
theorem eq_33 (a q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hcm : 0 < cm) (hm : 0 ≤ m i.rev) (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u : ℝ => eqPayoff a 0 q n thetaBar cm (Function.update m i u) i) (margNC a q n t - cm * t) t := by sorry

end CompOpacity.Disclosure
