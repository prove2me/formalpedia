-- Prove2me | Theorems.Thm_AVRideHailAuditF0557E82_IndependentPrice_proposition4_full_corrected
-- name    : AVRideHailAuditF0557E82.IndependentPrice.proposition4_full_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-28T00:37:30.19201+00:00
-- url     : https://prove2.me/theorems/d03a3820-1bf7-4402-919e-09db338845dd
-- title:
--   Proposition 4, Items 1 and 2 (corrected: endpoint equality in Item 2)
-- statement:
--   Let $a,t_2,V,w_0>0$, $0<r<1$ and $\alpha>0$ be the pickup-time, trip-time, rider-value and human-driver supply parameters. Fix any scenario with potential demand mass $m>0$. For positive demand $d$, put
--
--   $$
--   \widetilde a=r^{1/(r+1)}a^{1/(r+1)}+r^{-r/(r+1)}a^{1/(r+1)},\qquad
--   n(d)=\widetilde a d^{1/(r+1)}+t_2d,\qquad
--   \bar u(d)=dt_2/n(d),
--   $$
--   $$
--   p(d)=V(1-d/m),\qquad w(n)=w_0+\alpha n,\qquad q(d)=w(n(d))/\bar u(d),
--   $$
--   $$
--   B(d)=\frac{w_0}{n(d)}\,
--   \frac{\widetilde a r/[t_2(r+1)]}{\widetilde a(1-r)/[t_2(r+1)]+d^{r/(r+1)}}.
--   $$
--
--   Here $n$ is the minimal fleet, $\bar u$ its on-trip utilization, $p$ the inverse demand on $[0,m]$, $w$ the hourly reservation earnings, and $q$ the labor cost per ride-hour. Let $D>0$ be the greatest stable pure-HV equilibrium demand: $D\in[0,m]$ and $Dp(D)t_2=w(n(D))n(D)$, with stability as in Definition 1 and perturbations in $[0,m]$.
--
--   Both following assertions hold:
--
--   1. If $q$ is strictly decreasing in the ordinary order sense on $(0,D]$, then every pair of demands $h,z>0$ with $h+z\le m$ and $hp(h+z)t_2=w(n(h))n(h)$ satisfies
--
--      $$p(h+z)>p(D).$$
--
--   2. The full interval condition has the exact characterization
--
--      $$q\text{ strictly decreasing on }(0,D]\quad\Longleftrightarrow\quad\alpha\le B(D).$$
--
--   The first clause applies to each source coexistence outcome under either AV competition regime. The second identifies the precise supply-slope threshold, including equality at the endpoint. Together they preserve both items of Proposition 4; the already proved sufficient-condition price corollary alone does not give this characterization.
--
--   **Formalization Note** All demands and fleet sizes are real. Strict decrease means that $q(y)<q(x)$ whenever $0<x<y\le D$. No derivative-sign condition or threshold is a standing hypothesis. The published coexistence predicate records only the HV zero-profit condition, not the full source definition of a selected mixed equilibrium.
--
--   Differences from the source:
--   - correction: Item 2 asserts $\alpha<B(D)$ for ordinary strict decrease → Item 2 asserts $\alpha\le B(D)$; reason: with $r=1/2$, $a=2/(3\sqrt3)$, $t_2=w_0=1$, $\alpha=1/8$, $m=3/2$, $V=15/2$, $D=1$, one has $B(D)=\alpha$ and $q$ strictly decreasing on $(0,1]$, with $q\prime(1)=0$
--   - generalization: coexistence in the stable, selected market with loose labor, positive AV costs and AV dispatch/investment decisions → every positive independent-platform HV zero-profit pair, without loose-market or AV-cost, stability, optimality or investment restrictions; the ratio characterization does not require a mixed pair to exist; reason: each source coexistence outcome satisfies the retained demand-domain and HV zero-profit conditions (48), (51), so both source competition regimes specialize to this statement; the omitted conditions are unnecessary for these conclusions
--   - encoding: an arbitrary scenario $i$, positive benchmark $d^*_{HV,i}$, and the demand domain in D.3 → an arbitrary real mass $m>0$, a positive maximal stable benchmark $D$, and ordinary strict decrease on $\{d:0<d\le D\}$; reason: every source scenario is covered, admissible stability perturbations remain in $[0,m]$, and all ratio evaluations exclude undefined zero demand; no finite-grid approximation is introduced
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 25, Proposition 4 (Items 1 and 2); (19), p. 24; proof App. D.3, pp. 77–81

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

namespace AVRideHailAuditF0557E82.IndependentPrice

/-- Proposition 4, Items 1 and 2 (SSRN 3716491, 23 August 2023, p. 25;
proof pp. 77–81). Corrected: ordinary strict decrease allows endpoint equality
alpha = B(D), unlike strict negativity of the derivative at every point.
The price implication is stated for all positive independent-platform HV
zero-profit pairs, including the source's stable/optimal coexistence outcomes.
Unused loose-market and AV-cost/investment restrictions are not imposed.
For r = 1/2, a = 2/(3 sqrt(3)), t2 = w0 = 1, alpha = 1/8,
m = 3/2, V = 15/2, D = 1, the ratio is strictly decreasing on (0,1]
although alpha = B(1); this is the certified endpoint counterexample. -/
theorem proposition4_full_corrected
    (P : AVRideHail.PureHV.MarketParams)
    (ha : 0 < P.a) (hr0 : 0 < P.r) (hr1 : P.r < 1)
    (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0)
    (halpha : 0 < P.alpha)
    (m : ℝ) (hm : 0 < m) (D : ℝ) (hD : 0 < D)
    (hbenchmark : AVRideHail.PureHV.IsMaxStableEq P m D) :
    (StrictAntiOn (AVRideHail.IndepPlatform.hvRatio P) (Set.Ioc 0 D) →
      ∀ h z : ℝ, AVRideHail.IndepPlatform.IsIPMCoexistence P m h z →
        AVRideHail.PureHV.priceFn P m D <
          AVRideHail.PureHV.priceFn P m (h + z)) ∧
    (StrictAntiOn (AVRideHail.IndepPlatform.hvRatio P) (Set.Ioc 0 D) ↔
      P.alpha ≤ AVRideHail.IndepPlatform.alphaBound P D) := by sorry

end AVRideHailAuditF0557E82.IndependentPrice
