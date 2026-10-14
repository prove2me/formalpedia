-- Prove2me | Theorems.Thm_AVRideHail_PureHV_lemma1_nMin_strictMono_bijOn
-- name    : AVRideHail.PureHV.lemma1_nMin_strictMono_bijOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:35.904029+00:00
-- url     : https://prove2.me/theorems/252727fe-0c89-4fe7-b93a-efeba61d1391
-- title:
--   Lemma 1 Item 2, p. 38 — n̲ is strictly increasing and a bijection of [0, ∞), so its inverse d̄(n) exists
-- statement:
--   Let $a > 0$, $0 \le r < 1$ and $t_2 > 0$, and let $\underline{n}(d) = \tilde a\, d^{\frac{1}{r+1}} + t_2 d$ be the minimal supply level. Then $\underline{n}$ is strictly increasing on $[0,\infty)$ and maps $[0,\infty)$ bijectively onto $[0,\infty)$:
--   $$ \underline{n} : [0,\infty) \to [0,\infty) \text{ is a strictly increasing bijection.} $$
--   Consequently it has an inverse $\bar d(n)$ on $[0,\infty)$, the highest demand rate that a fleet of $n$ vehicles can serve.
--
--   The inverse $\bar d$ is what translates a fleet size into served demand in the paper's analysis of autonomous-vehicle capacity.
--
--   **Formalization Note** "Has an inverse function" is stated as `Set.BijOn` of $\underline{n}$ from $[0,\infty)$ onto $[0,\infty)$, together with strict monotonicity on $[0,\infty)$ (the proof's "strictly increasing"). The case $r = 0$ is included; there $\underline{n}(d) = (a + t_2) d$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 38, Lemma 1 Item 2; proof p. 39

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem lemma1_nMin_strictMono_bijOn (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) :
    StrictMonoOn (nMin P) (Set.Ici 0) ∧ Set.BijOn (nMin P) (Set.Ici 0) (Set.Ici 0) := by sorry

end AVRideHail.PureHV
