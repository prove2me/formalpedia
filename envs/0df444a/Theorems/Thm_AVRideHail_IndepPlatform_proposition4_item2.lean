-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_proposition4_item2
-- name    : AVRideHail.IndepPlatform.proposition4_item2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:32.41998+00:00
-- url     : https://prove2.me/theorems/60dbb10b-f9fe-4835-9878-52935ef41ffd
-- title:
--   Proposition 4 Item 2, p. 25 — the ratio condition on (0, d*] is equivalent to the α bound (19) at d*
-- statement:
--   Consider the ride-hailing market with $a>0$, $0<r<1$, $t_2>0$, $V>0$, HV supply curve $w(n)=w_0+\alpha n$ with $w_0>0$ and $\alpha>0$ (finitely elastic supply and a density effect). Let $d^*>0$. Then the labor cost per ride-hour $w(\underline n(d))/\bar u(d)$ has a strictly negative derivative at every $d\in(0,d^*]$ if and only if
--   $$\alpha<\frac{w_0}{\underline n(d^*)}\cdot\frac{\dfrac{\tilde a r}{t_2(r+1)}}{\dfrac{\tilde a(1-r)}{t_2(r+1)}+(d^*)^{\frac{r}{r+1}}},$$
--   which is condition (19) of the paper for a scenario whose pure-HV equilibrium demand is $d^*$.
--
--   The proposition translates the economic condition "labor cost per ride-hour falls with HV demand" into an explicit upper bound on the labor-cost slope $\alpha$.
--
--   **Formalization Note** The paper's "strictly decreasing in $d_{HV}$" is posed, as in the proof (App. D.3, p. 77: "strictly decreasing in $d_{HV}$ for $d\le d^*_{HV,i}$"; p. 81: "strictly decreasing at $d_{HV}$"), as a strictly negative derivative at every point of $(0,d^*]$. The reading "strictly decreasing function on $(0,d^*]$" would make the equivalence false at $\alpha=B(d^*)$, where the derivative vanishes only at $d^*$ and the ratio is still strictly decreasing. The statement holds for any $d^*>0$; the proof never uses that $d^*$ is an equilibrium, so it is stated in this generality.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 25, Proposition 4, Item 2; proof App. D.3.2, pp. 78–81, (231)–(243)

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- Proposition 4, Item 2, p. 25 (proof App. D.3.2, pp. 78–81), in the proof's pointwise reading:
the derivative of w(n̲(d))/ū(d) is strictly negative at every d ∈ (0, d*] iff α is below the
bound (19) evaluated at d*. Stated for any d* > 0. -/
theorem proposition4_item2 (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 < P.alpha)
    (dstar : ℝ) (hd : 0 < dstar) :
    (∀ d ∈ Set.Ioc 0 dstar, deriv (hvRatio P) d < 0) ↔ P.alpha < alphaBound P dstar := by sorry

end AVRideHail.IndepPlatform
