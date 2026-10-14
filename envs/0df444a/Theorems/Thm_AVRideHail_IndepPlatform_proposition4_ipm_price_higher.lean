-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_proposition4_ipm_price_higher
-- name    : AVRideHail.IndepPlatform.proposition4_ipm_price_higher
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:33.958822+00:00
-- url     : https://prove2.me/theorems/da3323a6-735b-45e6-bf0b-232e2b06495f
-- title:
--   Proposition 4, p. 25 — under (19), AV–HV coexistence on independent platforms strictly raises the price
-- statement:
--   Consider the ride-hailing market of Lian and van Ryzin with a density effect and finitely elastic HV supply: ETA function $t_1(s)=a s^{-r}$ with $a>0$ and $0<r<1$, trip time $t_2>0$, rider values uniform on $[0,V]$ with $V>0$, and HV supply curve $w(n)=w_0+\alpha n$ with $w_0>0$ and $\alpha>0$. Fix a demand scenario with potential demand mass $m>0$ and let $d^*_{HV}$ be the maximal stable equilibrium demand of the pure-HV market in it. Suppose
--   $$\alpha<\frac{w_0}{\underline n(d^*_{HV})}\cdot\frac{\dfrac{\tilde a r}{t_2(r+1)}}{\dfrac{\tilde a(1-r)}{t_2(r+1)}+(d^*_{HV})^{\frac{r}{r+1}}} \qquad (19)$$
--   for this scenario. If AVs and HVs serve the scenario together on independent platforms — HVs serve $d_{HV}>0$, AVs serve $d_{AV}>0$, $d_{HV}+d_{AV}\le m$, and HV revenue equals HV cost,
--   $$d_{HV}\,p(d_{HV}+d_{AV})\,t_2=w(\underline n(d_{HV}))\,\underline n(d_{HV}),$$
--   then the market price is strictly higher than in the pure-HV market:
--   $$p(d^*_{HV})<p(d_{HV}+d_{AV}),$$
--   where $p(d)=V(1-d/m)$ is the inverse demand.
--
--   This is the content of Proposition 4, Items 1 and 2 combined, as it is used in §6.1.2 and in Proposition 3, Item 2: when HV labor is elastic enough, splitting dispatch between an HV platform and an AV platform destroys more density-driven efficiency than it saves in labor cost, so riders pay more.
--
--   **Formalization Note** Coexistence records only the HV side of the independent-platform equilibrium (Definition 2's (48) with $n_{HV}=\underline n(d_{HV})$, (51)); the AV fleet choice and the stability of Definition 3 are not assumed, which generalizes the statement. The loose-market Assumption 2 (in the form (33)), which §6 assumes throughout, is not needed and is not assumed. The pure-HV equilibrium $d^*_{HV}$ is any number with the maximal-stable-equilibrium property (Definition 1 with $\varepsilon$ restricted to keep $d^*\pm\varepsilon$ in $[0,m]$), not a chosen one.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 25, Proposition 4 (Items 1 and 2); (19), p. 24; proof App. D.3, pp. 77–81

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- Proposition 4 (Items 1 and 2), p. 25, proof App. D.3, pp. 77–81: with α > 0, r > 0, if (19)
holds for the scenario, every coexistence equilibrium of the independent platform market has a
strictly higher price than the pure-HV maximal stable equilibrium. -/
theorem proposition4_ipm_price_higher (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 < P.alpha)
    (m : ℝ) (hm : 0 < m) (dstar : ℝ) (hdstar : AVRideHail.PureHV.IsMaxStableEq P m dstar)
    (h19 : P.alpha < alphaBound P dstar)
    (dHV dAV : ℝ) (hco : IsIPMCoexistence P m dHV dAV) :
    AVRideHail.PureHV.priceFn P m dstar < AVRideHail.PureHV.priceFn P m (dHV + dAV) := by sorry

end AVRideHail.IndepPlatform
