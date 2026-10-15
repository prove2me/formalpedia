-- Prove2me | Theorems.Thm_DigitalPrivacy_Strategy_proposition_1
-- name    : DigitalPrivacy.Strategy.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:44.570707+00:00
-- url     : https://prove2.me/theorems/80bd1de8-1f94-4806-b73c-ea5270d3fc42
-- title:
--   Proposition 1, p. 10 — for C > 0 the users–adversaries subgame has the unique equilibrium (3), and consumer surplus is ā*²/2
-- statement:
--   Fix a data strategy $(\xi, C)$ with $\xi \in [0,1]$ and protection level $C > 0$, and parameters $0 \le \beta < 1$, $0 \le \rho < 1$. Users have utility $U(a, \bar a) = a - \tfrac12 a^2 + \beta a\bar a + (\rho - \omega) a\xi$ over activity $a \ge 0$, and the mass of active adversaries is $\omega = \xi\bar a/C$.
--
--   Then the users–adversaries subgame has a unique equilibrium: a pair $(\bar a, \omega)$ is an equilibrium if and only if
--   $$\bar a = \bar a^*(\xi, C) = \frac{C(1+\rho\xi)}{C(1-\beta)+\xi^2}, \qquad \omega = \omega^*(\xi, C) = \frac{\xi\bar a^*(\xi, C)}{C}.$$
--   Moreover, each user's equilibrium utility, which is the consumer surplus, equals
--   $$U\big(\bar a^*(\xi, C), \bar a^*(\xi, C)\big)\Big|_{\omega = \omega^*} = \mathrm{CS}(\xi, C) = \tfrac12\,\bar a^*(\xi, C)^2 .$$
--
--   This identifies the users' and adversaries' behaviour behind every profit and welfare comparison in the paper: the business's profit (2) is a function of $\bar a^*$ alone.
--
--   **Formalization Note** An equilibrium is a pair $(\bar a, \omega)$: since users are identical and their utility is strictly concave in their own activity, every user's best reply is the same number, which is then the average activity. The best reply is taken over $a \ge 0$ (activity levels are in $\mathbb R_+$). The statement requires $C > 0$, since $\omega = \xi\bar a/C$ is undefined at $C = 0$. The "Furthermore" part of Proposition 1 is a separate item.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 10, Proposition 1, (3)–(4); proof App. A.1, p. 28

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Strategy

/-- Proposition 1, p. 10, first part: for a data strategy `(ξ, C)` with `ξ ∈ [0, 1]` and `C > 0`,
the users–adversaries subgame has the unique (symmetric) equilibrium `(ā*(ξ, C), ω*(ξ, C))` of (3),
and the users' equilibrium utility is the consumer surplus `CS(ξ, C) = ā*(ξ, C)² / 2` of (4). -/
theorem proposition_1 (β ρ ξ C : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (hC : 0 < C) :
    (∀ ā ω : ℝ, IsSubgameEq β ρ ξ C ā ω ↔ (ā = abar β ρ ξ C ∧ ω = omegaStar β ρ ξ C)) ∧
    userUtil β ρ ξ (omegaStar β ρ ξ C) (abar β ρ ξ C) (abar β ρ ξ C) = CS β ρ ξ C := by sorry

end DigitalPrivacy.Strategy
