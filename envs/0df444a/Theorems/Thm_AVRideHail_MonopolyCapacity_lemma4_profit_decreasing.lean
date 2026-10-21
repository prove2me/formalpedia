-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_lemma4_profit_decreasing
-- name    : AVRideHail.MonopolyCapacity.lemma4_profit_decreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:24.107996+00:00
-- url     : https://prove2.me/theorems/135ff197-c64a-4e39-9a34-7fc6cb33d84e
-- title:
--   Lemma 4, p. 84 — the AV-only total variable profit strictly decreases beyond n*_{HV,i}
-- statement:
--   Consider a scenario with potential demand mass $m > 0$ in a market with $a > 0$, $0 < r < 1$, $t_2 > 0$, $V > 0$, constant HV reservation earnings $w_0 > 0$ ($\alpha = 0$), and AV variable cost $c_v > 0$. Suppose the market is loose (condition (33)) and $d^*$ is its maximal stable pure-HV equilibrium, with $n^*_{HV} = \underline{n}(d^*)$. When AVs serve the market alone with a fleet of $n_{AV}$ vehicles, they serve the demand $d_{AV} = \bar d(n_{AV})$, and the total variable profit of the monopoly supplier is (250)
--   $$p(d_{AV})\, d_{AV}\, t_2 - c_v n_{AV}.$$
--   This function of $n_{AV}$ is strictly decreasing on $[n^*_{HV}, \infty)$.
--
--   Lemma 4 is the reason a monopoly never deploys more AVs than the pure-HV fleet size: beyond $n^*_{HV}$ the loss in price outweighs the extra demand served.
--
--   **Formalization Note.** The paper's Assumption 2 is written as the loose-market condition (33) of App. B.1.1. The paper's §6.2 sets $\alpha = 0$; the remaining parameter positivity is the paper's standing setting. The domain $[n^*_{HV}, \infty)$ is not cut at $\underline{n}(m)$: for larger fleets the formula's price is negative, as on the page.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 84, Lemma 4, with (250) on p. 83

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem lemma4_profit_decreasing (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : P.alpha = 0)
    (cv : ℝ) (hcv : 0 < cv) (m : ℝ) (hm : 0 < m) (hloose : AVRideHail.PureHV.LooseMarket P m)
    (dstar : ℝ) (hdstar : AVRideHail.PureHV.IsMaxStableEq P m dstar) :
    StrictAntiOn (fun n => AVRideHail.PureHV.priceFn P m (dBar P n) * dBar P n * P.t2 - cv * n)
      (Set.Ici (AVRideHail.PureHV.nMin P dstar)) := by sorry

end AVRideHail.MonopolyCapacity
