-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_eq_44
-- name    : CompOpacity.Disclosure.eq_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:34.124832+00:00
-- url     : https://prove2.me/theorems/5bb0119e-3d85-40f6-a0ee-8b7b11d489f4
-- title:
--   (44), p. 36 (a < 1/2 added) — at b = 1, ∂Π*/∂m = (m + q − (1−2a)n)/(2(1−2a)[q+m+(1−2a)n]³) − c_m m
-- statement:
--   At competition intensity $b = 1$, let $a \in [0, \tfrac12)$, $q, n, \bar\theta, c_m > 0$ and let the other FI's precision be $m_{-i} \ge 0$. Let $\Pi^*_i(m_i)$ be FI $i$'s payoff (9), net of the disclosure cost, when investors play the linear equilibrium. Then at every $m_i > 0$,
--   $$\frac{\partial \Pi^*_i}{\partial m_i} = \frac{m_i + q - (1-2a)n}{2(1-2a)[q + m_i + (1-2a)n]^3} - c_m m_i,$$
--   independently of $m_{-i}$.
--
--   Comparing this marginal payoff with (33) is how the paper compares disclosure with and without competition.
--
--   **Formalization Note** The bound $a < \tfrac12$ is added to the model's $a \in [0, \tfrac12]$: at $a = \tfrac12$ and $b = 1$ the investors' fixed point has no solution and the formula divides by $0$.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), pp. 35–36, (43)–(44), proof of Proposition 4

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- (44), p. 36 (with (43), p. 35): at competition intensity `b = 1` and `a ∈ [0, 1/2)`, at every
precision `t > 0` FI `i`'s equilibrium payoff net of the disclosure cost has derivative in its own
precision `∂Π*ᵢ/∂mᵢ = (mᵢ + q − (1 − 2a)n)/(2(1 − 2a)[q + mᵢ + (1 − 2a)n]³) − c_m mᵢ`, whatever the
other FI's precision `m₋ᵢ ≥ 0`. The bound `a < 1/2` is added: at `a = 1/2`, `b = 1` there is no
linear investor equilibrium. -/
theorem eq_44 (a q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hcm : 0 < cm) (hm : 0 ≤ m i.rev) (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u : ℝ => eqPayoff a 1 q n thetaBar cm (Function.update m i u) i) (margStar a q n t - cm * t) t := by sorry

end CompOpacity.Disclosure
