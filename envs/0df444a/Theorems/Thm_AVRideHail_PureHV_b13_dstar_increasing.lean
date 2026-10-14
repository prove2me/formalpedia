-- Prove2me | Theorems.Thm_AVRideHail_PureHV_b13_dstar_increasing
-- name    : AVRideHail.PureHV.b13_dstar_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:41.178246+00:00
-- url     : https://prove2.me/theorems/ac569689-7415-4494-80b7-3909f899b724
-- title:
--   App. B.1.3, p. 43 — the maximal stable equilibrium demand is increasing in the potential demand mass
-- statement:
--   Consider a pure-HV market with parameters $a > 0$, $0 \le r < 1$, $t_2 > 0$, $V > 0$, $w_0 > 0$, $\alpha \ge 0$, and two demand scenarios with potential demand masses $0 < m < m'$, both satisfying the loose labor market condition (33). If $d$ is the maximal stable equilibrium demand of the scenario with mass $m$ and $d'$ that of the scenario with mass $m'$, then
--   $$ d < d'. $$
--
--   This is Item 2 of Proposition 1 for a pair of scenarios: a denser market serves strictly more demand.
--
--   **Formalization Note** "Increasing" is read as strictly increasing, as the proof derives. The loose-market condition is required of both scenarios, as Proposition 1's proof assumes Assumption 2 in every scenario.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. B.1.3, p. 43, (39)–(40)

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem b13_dstar_increasing (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (m m' : ℝ) (hm : 0 < m) (hmm' : m < m') (hloose : LooseMarket P m)
    (hloose' : LooseMarket P m') (d d' : ℝ) (hd : IsMaxStableEq P m d)
    (hd' : IsMaxStableEq P m' d') :
    d < d' := by sorry

end AVRideHail.PureHV
