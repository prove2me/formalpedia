-- Prove2me | Theorems.Thm_AVRideHail_PureHV_lemma1_open_cars_minimizer
-- name    : AVRideHail.PureHV.lemma1_open_cars_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:33.571841+00:00
-- url     : https://prove2.me/theorems/07901ad0-487d-424d-8812-9aa0f1590679
-- title:
--   Lemma 1 Item 1, p. 38 — n̲(d) = ã d^{1/(r+1)} + t₂d is the minimal supply, attained uniquely at (26)
-- statement:
--   Let $a > 0$, $0 < r < 1$ and $t_2 > 0$. To serve a demand rate $d > 0$ with $s$ open cars, a fleet of $n(s) = s + d\,(t_1(s) + t_2)$ vehicles is needed, where $t_1(s) = a s^{-r}$ is the pickup time (equation (23)). Let
--   $$ s_0 = (ra)^{\frac{1}{r+1}}\, d^{\frac{1}{r+1}} \qquad (26).$$
--   Then $s_0 > 0$, the fleet size at $s_0$ equals the minimal supply level,
--   $$ s_0 + d\,(a s_0^{-r} + t_2) = \underline{n}(d) = \tilde a\, d^{\frac{1}{r+1}} + t_2 d, $$
--   and every other number of open cars $s > 0$, $s \ne s_0$, needs a strictly larger fleet: $\underline{n}(d) < s + d\,(a s^{-r} + t_2)$.
--
--   This is the closed form of the minimal supply level that every equilibrium of the paper is built on: an HV market serving demand $d$ in equilibrium dispatches exactly $\underline{n}(d)$ drivers.
--
--   **Formalization Note** The minimization is over $s > 0$, since $s^{-r}$ is meaningless at $s = 0$. The hypothesis $r > 0$ is added: for $r = 0$ the function $s + d(a + t_2)$ has infimum $(a+t_2)d = \underline{n}(d)$ over $s > 0$ but no minimizer, and $s_0 = 0$. The definitions of $\tilde a$ and $\underline{n}$ are those of the Model file.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 38, Lemma 1 Item 1; p. 39, (26)–(29) of its proof

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem lemma1_open_cars_minimizer (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (d : ℝ) (hd : 0 < d) (s0 : ℝ)
    (hs0 : s0 = (P.r * P.a) ^ (1 / (P.r + 1)) * d ^ (1 / (P.r + 1))) :
    0 < s0 ∧ s0 + d * (P.a * s0 ^ (-P.r) + P.t2) = nMin P d ∧
      ∀ s : ℝ, 0 < s → s ≠ s0 → nMin P d < s + d * (P.a * s ^ (-P.r) + P.t2) := by sorry

end AVRideHail.PureHV
