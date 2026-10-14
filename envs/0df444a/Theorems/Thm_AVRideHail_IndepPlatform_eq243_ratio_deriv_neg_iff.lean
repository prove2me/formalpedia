-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_eq243_ratio_deriv_neg_iff
-- name    : AVRideHail.IndepPlatform.eq243_ratio_deriv_neg_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:33.347932+00:00
-- url     : https://prove2.me/theorems/53be80e6-f4fa-4bbb-9061-a1086ea03e14
-- title:
--   (243), App. D.3.2, p. 81 — w(n̲(d))/ū(d) is strictly decreasing at d iff α is below the bound
-- statement:
--   Consider the ride-hailing market with ETA constants $a>0$, $0<r<1$, trip time $t_2>0$, HV supply curve $w(n)=w_0+\alpha n$ with $w_0>0$ and $\alpha>0$ (and rider value cap $V>0$). Let $\underline n(d)=\tilde a\,d^{1/(r+1)}+t_2 d$ be the minimal fleet size and $\bar u(d)=d\,t_2/\underline n(d)$ the utilization rate. Then for every demand level $d>0$, the labor cost per ride-hour $d\mapsto w(\underline n(d))/\bar u(d)$ has a strictly negative derivative at $d$ if and only if
--   $$\alpha<\frac{w_0}{\underline n(d)}\cdot\frac{\dfrac{\tilde a r}{t_2(r+1)}}{\dfrac{\tilde a(1-r)}{t_2(r+1)}+d^{\frac{r}{r+1}}} .$$
--
--   This pointwise criterion is the core computation behind Proposition 4: it says when the efficiency loss from a thinner HV platform outweighs the saving in labor cost.
--
--   **Formalization Note** "Strictly decreasing at $d$" is read, as in the proof, as a strictly negative derivative (Mathlib's `deriv`) at $d$. The ratio is differentiable at every $d>0$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. D.3.2, pp. 78–81, (232)–(243); the statement after (243), p. 81

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- (243), App. D.3.2, p. 81: at d > 0, w(n̲(d))/ū(d) has a strictly negative derivative iff
α < (w₀/n̲(d)) · (ãr/(t₂(r+1))) / (ã(1−r)/(t₂(r+1)) + d^{r/(r+1)}). -/
theorem eq243_ratio_deriv_neg_iff (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 < P.alpha)
    (d : ℝ) (hd : 0 < d) :
    deriv (hvRatio P) d < 0 ↔ P.alpha < alphaBound P d := by sorry

end AVRideHail.IndepPlatform
