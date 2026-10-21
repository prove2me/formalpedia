-- Prove2me | Theorems.Thm_AVRideHail_IndepPlatform_alphaBound_strictAntiOn
-- name    : AVRideHail.IndepPlatform.alphaBound_strictAntiOn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:04.255809+00:00
-- url     : https://prove2.me/theorems/e3167aba-fdd7-4e8d-9d73-ea0ce63071ce
-- title:
--   App. D.3.2, p. 81 — the right-hand side of (243) is strictly decreasing in d
-- statement:
--   Let $a>0$, $0<r<1$, $t_2>0$ and $w_0>0$. The bound of (19) and (243),
--   $$B(d)=\frac{w_0}{\underline n(d)}\cdot\frac{\dfrac{\tilde a r}{t_2(r+1)}}{\dfrac{\tilde a(1-r)}{t_2(r+1)}+d^{\frac{r}{r+1}}},$$
--   is strictly decreasing on $(0,\infty)$: if $0<d_1<d_2$ then $B(d_2)<B(d_1)$.
--
--   Consequently, the condition $\alpha<B(d^*_{HV})$ at the pure-HV equilibrium demand implies $\alpha<B(d)$ at every smaller demand level, which is how the pointwise criterion (243) is turned into a statement about a whole interval.
--
--   **Formalization Note** The remaining standing parameters ($V>0$, $\alpha\ge0$) are carried for uniformity and are unused.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. D.3.2, p. 81, the sentence after (243); also p. 24, footnote 12

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHail.IndepPlatform

/-- App. D.3.2, p. 81, the sentence after (243): the right-hand side of (243) is strictly
decreasing in d on d > 0. -/
theorem alphaBound_strictAntiOn (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha) :
    StrictAntiOn (alphaBound P) (Set.Ioi 0) := by sorry

end AVRideHail.IndepPlatform
