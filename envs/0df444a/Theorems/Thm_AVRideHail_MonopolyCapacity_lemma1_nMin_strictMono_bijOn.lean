-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_lemma1_nMin_strictMono_bijOn
-- name    : AVRideHail.MonopolyCapacity.lemma1_nMin_strictMono_bijOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:19.084378+00:00
-- url     : https://prove2.me/theorems/f7e6b90f-8e6a-4c4c-bd8c-e56e6250b1c0
-- title:
--   Lemma 1 Item 2, p. 38 — n̲ is strictly increasing and a bijection of [0, ∞)
-- statement:
--   Let $a > 0$, $0 \le r < 1$ and $t_2 > 0$, and let $\underline{n}(d) = \tilde a\, d^{1/(r+1)} + t_2 d$ be the minimal supply level of Lemma 1, with $\tilde a = r^{1/(r+1)} a^{1/(r+1)} + r^{-r/(r+1)} a^{1/(r+1)}$. Then $\underline{n}$ is strictly increasing on $[0, \infty)$ and maps $[0, \infty)$ bijectively onto $[0, \infty)$:
--   $$\underline{n} : [0,\infty) \to [0,\infty) \text{ is a strictly increasing bijection.}$$
--   Consequently $\underline{n}$ has an inverse $\bar d(n)$ on $[0, \infty)$, the highest demand rate that a fleet of $n$ vehicles can serve.
--
--   This is the fact that makes the AV demand $\bar d(n_{AV})$ in the profit function (251) well defined.
--
--   **Formalization Note.** The statement is the same text, up to namespace, as the copy in the pure-HV mission of this series. At $r = 0$ Lean's conventions give $\tilde a = a$ and $\underline{n}(d) = (a + t_2) d$, matching the paper's $r = 0$ case.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 38, Lemma 1 Item 2

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem lemma1_nMin_strictMono_bijOn (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) :
    StrictMonoOn (AVRideHail.PureHV.nMin P) (Set.Ici 0) ∧ Set.BijOn (AVRideHail.PureHV.nMin P) (Set.Ici 0) (Set.Ici 0) := by sorry

end AVRideHail.MonopolyCapacity
