-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_d31_dHV_lt_dstar
-- name    : AVRideHail.IndepPlatform.d31_dHV_lt_dstar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:41.479667+00:00
-- url     : https://prove2.me/theorems/c4624019-4f99-4403-9ce8-0100962b85db
-- title:
--   App. D.3.1, p. 77 — under coexistence on independent platforms, HV demand is strictly below d*_{HV,i}
-- statement:
--   Consider the ride-hailing market with $a>0$, $0\le r<1$, $t_2>0$, $V>0$, $w_0>0$, $\alpha\ge0$, and a demand scenario with potential demand mass $m>0$. Let $d^*_{HV}$ be the maximal stable equilibrium demand of the pure-HV market in this scenario. Suppose AVs and HVs serve the scenario together on independent platforms: HVs serve $d_{HV}>0$, AVs serve $d_{AV}>0$, $d_{HV}+d_{AV}\le m$, and
--   $$d_{HV}\,p(d_{HV}+d_{AV})\,t_2=w(\underline n(d_{HV}))\,\underline n(d_{HV}).$$
--   Then
--   $$d_{HV}<d^*_{HV}.$$
--
--   AV entry on a separate platform squeezes HV demand strictly below its pure-HV level; this is the first step of the proof of Proposition 4.
--
--   **Formalization Note** Only the HV side of the independent-platform equilibrium is assumed (Definition 2's (48) with (51)); the AV fleet choice and the stability of Definition 3 are not, which makes the statement more general. The claim holds for $r=0$ and $\alpha=0$ as well, so the hypotheses are the weaker $0\le r$, $0\le\alpha$. The loose-market condition (33) is not assumed. $d^*_{HV}$ is taken as any number satisfying the maximal-stable-equilibrium property, not chosen.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. D.3.1, p. 77, first claim; proved pp. 77–78, (225)–(228)

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- App. D.3.1, p. 77 (proved pp. 77–78): in a coexistence equilibrium of the independent
platform market, the HV demand is strictly below the pure-HV maximal stable equilibrium demand. -/
theorem d31_dHV_lt_dstar (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (m : ℝ) (hm : 0 < m) (dstar : ℝ) (hdstar : AVRideHail.PureHV.IsMaxStableEq P m dstar)
    (dHV dAV : ℝ) (hco : IsIPMCoexistence P m dHV dAV) :
    dHV < dstar := by sorry

end AVRideHail.IndepPlatform
