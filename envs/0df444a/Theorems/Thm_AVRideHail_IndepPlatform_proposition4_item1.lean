-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_proposition4_item1
-- name    : AVRideHail.IndepPlatform.proposition4_item1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:42.04252+00:00
-- url     : https://prove2.me/theorems/5b645dc9-8eb5-49bc-957a-89ba71a9015b
-- title:
--   Proposition 4 Item 1, p. 25 — if w(n̲)/ū is strictly decreasing on (0, d*], the coexistence price is strictly higher
-- statement:
--   Consider the ride-hailing market with $a>0$, $0<r<1$, $t_2>0$, $V>0$, HV supply curve $w(n)=w_0+\alpha n$ with $w_0>0$ and $\alpha>0$, and a scenario with potential demand mass $m>0$ whose pure-HV maximal stable equilibrium demand is $d^*_{HV}$. Assume that the labor cost per ride-hour $d\mapsto w(\underline n(d))/\bar u(d)$ is strictly decreasing on $(0,d^*_{HV}]$. If AVs and HVs serve the scenario together on independent platforms, with HV demand $d_{HV}>0$, AV demand $d_{AV}>0$, $d_{HV}+d_{AV}\le m$ and
--   $$d_{HV}\,p(d_{HV}+d_{AV})\,t_2=w(\underline n(d_{HV}))\,\underline n(d_{HV}),$$
--   then the price is strictly higher than in the pure-HV market:
--   $$p(d^*_{HV})<p(d_{HV}+d_{AV}).$$
--
--   Here $p(d)=V(1-d/m)$ is the inverse demand; $p(d^*_{HV})$ is the pure-HV equilibrium price and $p(d_{HV}+d_{AV})$ the independent-platform price.
--
--   **Formalization Note** The monotonicity hypothesis is taken on $(0,d^*_{HV}]$, the range the proof uses (App. D.3, p. 77: "for $d\le d^*_{HV,i}$"); the ratio is not meaningful at $d=0$. Only the HV side of the independent-platform equilibrium is assumed (Definition 2's (48) with (51)); the AV fleet choice and Definition 3's stability are not, a generalization. The loose-market condition (33) is not assumed.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 25, Proposition 4, Item 1; proof App. D.3.1, pp. 77–78, (223)–(230)

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- Proposition 4, Item 1, p. 25 (proof App. D.3.1, pp. 77–78): if w(n̲(d))/ū(d) is strictly
decreasing for d ∈ (0, d*], a coexistence equilibrium of the independent platform market has a
strictly higher price than the pure-HV market. -/
theorem proposition4_item1 (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 < P.alpha)
    (m : ℝ) (hm : 0 < m) (dstar : ℝ) (hdstar : AVRideHail.PureHV.IsMaxStableEq P m dstar)
    (hdec : StrictAntiOn (hvRatio P) (Set.Ioc 0 dstar))
    (dHV dAV : ℝ) (hco : IsIPMCoexistence P m dHV dAV) :
    AVRideHail.PureHV.priceFn P m dstar < AVRideHail.PureHV.priceFn P m (dHV + dAV) := by sorry

end AVRideHail.IndepPlatform
