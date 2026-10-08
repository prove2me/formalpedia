-- Prove2me | Theorems.Thm_CalibratedCE_Generic_ae_limitSet_eq_CESet
-- name    : CalibratedCE.Generic.ae_limitSet_eq_CESet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:12:30.222828+00:00
-- url     : https://prove2.me/theorems/ae2540c9-10da-4d9d-8562-bb184f911628
-- title:
--   Theorem 2 (p. 47) — for almost every game, $\lambda(G) = \pi(G)$
-- statement:
--   Fix finite strategy sets $S(1)$, $S(2)$ with $m$ and $n$ elements. A game $G = (u_1,u_2)$ is a pair of real $m\times n$ payoff matrices, i.e. a point of $\mathbb{R}^{2mn}$; "a set of games is of measure zero if the corresponding set of points in $\mathbb{R}^{2mn}$ has Lebesgue measure zero" (p. 46). Let $\pi(G)$ be the set of correlated equilibria of $G$ and $\lambda(G)$ the set of limit points of calibrated forecasts: the joint distributions $D$ for which there are stationary deterministic best-reply functions $R_1,R_2$ and history-dependent forecasting rules, calibrated against the opponent's plays, such that when each player plays $R_i$ of its forecast the empirical joint distribution of play converges to $D$.
--
--   **Theorem.** For almost every game,
--   $$\lambda(G) = \pi(G).$$
--   "In other words, for almost every game, the set of distributions which calibrated learning rules can converge to is identical to the set of correlated equilibriums." (p. 47)
--
--   The inclusion $\lambda(G)\subseteq\pi(G)$ holds for every game (Theorem 1). The converse says that every correlated equilibrium is reached, as a genuine limit, by some calibrated forecasting rules with best replies; so calibration alone cannot single out any particular correlated equilibrium. The example of p. 48 shows that the converse fails for some non-generic games.
--
--   **Formalization Note** "Almost every" is with respect to Lebesgue measure on the pair of payoff matrices, $\mathbb{R}^{mn}\times\mathbb{R}^{mn}$. When $m = 0$ or $n = 0$ both sides are empty.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 47, Theorem (Theorem 2)

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet

namespace CalibratedCE.Generic

theorem ae_limitSet_eq_CESet (m n : ℕ) :
    ∀ᵐ G : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) ∂MeasureTheory.volume,
      LimitSet G.1 G.2 = CESet G.1 G.2 := by sorry

end CalibratedCE.Generic
