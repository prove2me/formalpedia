-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_eq240_nMin_log_derivative_bounds
-- name    : AVRideHail.IndepPlatform.eq240_nMin_log_derivative_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:02.799257+00:00
-- url     : https://prove2.me/theorems/d1d2e884-7d50-4ce4-97b2-8e7e0bd0b7d3
-- title:
--   (240), App. D.3.2, p. 80 — 1/(2d) < n̲′(d)/n̲(d) < 1/d
-- statement:
--   Let $a>0$, $0<r<1$ and $t_2>0$, and let $\underline n(d)=\tilde a\,d^{1/(r+1)}+t_2 d$ be the minimal HV fleet size needed to serve demand $d$, with $\tilde a=r^{1/(r+1)}a^{1/(r+1)}+r^{-r/(r+1)}a^{1/(r+1)}$. Then for every $d>0$ the logarithmic derivative of $\underline n$ lies strictly between $1/(2d)$ and $1/d$:
--   $$\frac{1}{2d}<\frac{\underline n'(d)}{\underline n(d)}<\frac1d .$$
--
--   Equivalently, the elasticity $d\,\underline n'(d)/\underline n(d)$ of the minimal fleet size lies strictly between $1/2$ and $1$: the fleet grows less than proportionally with demand (the density effect) but faster than its square root. This is the inequality that makes the sign analysis of $w(\underline n(d))/\bar u(d)$ in the proof of Proposition 4 well defined.
--
--   **Formalization Note** $\underline n'(d)$ is Mathlib's `deriv` of $\underline n$ at $d$. The other standing parameters of the model ($V>0$, $w_0>0$, $\alpha\ge0$) are carried as hypotheses for uniformity with the rest of the mission; they play no role.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. D.3.2, p. 80, (240); verified pp. 80–81

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- (240), App. D.3.2, p. 80 (proved pp. 80–81): for d > 0, 1/(2d) < n̲′(d)/n̲(d) < 1/d. -/
theorem eq240_nMin_log_derivative_bounds (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (d : ℝ) (hd : 0 < d) :
    1 / (2 * d) < deriv (AVRideHail.PureHV.nMin P) d / AVRideHail.PureHV.nMin P d ∧ deriv (AVRideHail.PureHV.nMin P) d / AVRideHail.PureHV.nMin P d < 1 / d := by sorry

end AVRideHail.IndepPlatform
