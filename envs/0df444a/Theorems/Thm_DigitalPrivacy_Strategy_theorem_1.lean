-- Prove2me | Theorems.Thm_DigitalPrivacy_Strategy_theorem_1
-- name    : DigitalPrivacy.Strategy.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:46.74152+00:00
-- url     : https://prove2.me/theorems/8a464154-ed53-49f5-b592-b85722d951fe
-- title:
--   Theorem 1, p. 11 — the data strategy (5)–(6) maximizes the business's profit, and ξ*, C* weakly increase in P
-- statement:
--   A digital business stores a fraction $\xi \in [0,1]$ of its users' activity and protects it at level $C \ge 0$, earning profit
--   $$\Pi(\xi, C) = (1-P)\,\bar a^*(\xi, C) + P\,\xi\bar a^*(\xi, C) - \psi C, \qquad \bar a^*(\xi, C) = \frac{C(1+\rho\xi)}{C(1-\beta)+\xi^2},$$
--   where $\bar a^*$ is the users' equilibrium activity (with $\bar a^*(0, C) = 1/(1-\beta)$), $\beta$ the network effect, $\rho$ the users' benefit from stored data, $\psi$ the unit cost of protection and $P$ the data-driven share of revenue.
--
--   Fix $0 \le \beta < 1$, $0 < \rho < 1$ and $\psi > 0$. For $P \in (0, 1]$ let
--   $$\xi^\star(P) = \max\Big\{0, \min\Big\{1, \frac{1}{2P\rho}\Big(-(1-P)\rho - P + |P-(1-P)\rho|\sqrt{\frac{\psi}{\max\{0, \psi - P\rho\}}}\Big)\Big\}\Big\},$$
--   $$C^\star(P) = \frac{\xi^\star}{1-\beta}\Big(-\xi^\star + \sqrt{\tfrac1\psi(1+\rho\xi^\star)(1-P(1-\xi^\star))}\Big),$$
--   where $\xi^\star = 1$ when $\psi \le P\rho$ (the root is then $+\infty$). Then:
--
--   1. for every $P \in (0, 1]$, $(\xi^\star(P), C^\star(P))$ lies in $[0,1] \times [0,\infty)$ and maximizes $\Pi$ over $[0,1] \times [0,\infty)$;
--   2. $P \mapsto \xi^\star(P)$ and $P \mapsto C^\star(P)$ are weakly increasing on $(0, 1]$.
--
--   A more data-driven business thus both collects more data and protects it more: data collection and data protection are complements.
--
--   **Formalization Note**
--   1. The paper allows $\rho \in [0,1)$, $\psi \ge 0$ and $P \in [0,1]$. Formula (5) divides by $2P\rho$, so the statement assumes $P > 0$ and $\rho > 0$ (as $P \to 0$, (5) does not tend to $0$); $C^\star$ contains $1/\psi$, so it assumes $\psi > 0$. Monotonicity is claimed on $P \in (0,1]$.
--   2. "The data collection and protection are" is formalized as "is a maximizer": the maximizer is not always unique (at $P = \rho/(1+\rho)$, $\psi = \rho^2/(1+\rho)$ the strategies $(0,0)$ and $(1, C_h(1))$ tie).
--   3. $\bar a^*(0, 0) = 1/(1-\beta)$, the paper's value (App. A.2–A.3), replaces the $0/0$ of (3); with $0$ there the statement would be false for large $\psi$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 11, Theorem 1, (5)–(6); proof App. A.2–A.3, pp. 29–33, Online App. B

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Strategy

/-- Theorem 1, p. 11: for fixed `0 ≤ β < 1`, `0 < ρ < 1`, `ψ > 0`, and every revenue share
`P ∈ (0, 1]`, the data strategy `(ξ*, C*)` of (5)–(6) is feasible and maximizes the business's
profit `Π` over `[0, 1] × [0, ∞)`; and both `P ↦ ξ*` and `P ↦ C*` are weakly increasing on
`(0, 1]`. -/
theorem theorem_1 (β ρ ψ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hψ : 0 < ψ) :
    (∀ P : ℝ, 0 < P → P ≤ 1 → IsBusinessOpt β ρ ψ P (xiStar ρ ψ P) (CStar β ρ ψ P)) ∧
    MonotoneOn (fun P => xiStar ρ ψ P) (Set.Ioc 0 1) ∧
    MonotoneOn (fun P => CStar β ρ ψ P) (Set.Ioc 0 1) := by sorry

end DigitalPrivacy.Strategy
