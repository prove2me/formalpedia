-- Prove2me | Theorems.Thm_AVRideHail_PureHV_lemma2_utilization
-- name    : AVRideHail.PureHV.lemma2_utilization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:41.188869+00:00
-- url     : https://prove2.me/theorems/fcab7c45-cef2-4081-ab36-14d490169735
-- title:
--   Lemma 2 (Utilization), p. 39 — ū(d) is increasing and strictly concave, ū(0) = 0, ū(d) → 1
-- statement:
--   Let $a > 0$, $0 < r < 1$ and $t_2 > 0$, and let
--   $$ \bar u(d) = \frac{d\,t_2}{\underline{n}(d)} = \frac{d\,t_2}{\tilde a\, d^{1/(r+1)} + t_2 d} $$
--   be the maximal utilization of a fleet serving demand rate $d$ (equation (22)). Then:
--
--   1. $\bar u$ is strictly increasing on $[0,\infty)$;
--   2. $\bar u$ is strictly concave on $[0,\infty)$;
--   3. $\bar u(0) = 0$;
--   4. $\bar u(d) \to 1$ as $d \to \infty$.
--
--   This is the density effect of the paper: a larger demand rate lets a fleet spend a larger fraction of its time on trips.
--
--   **Formalization Note** The hypothesis $r > 0$ is added; the page leaves it implicit, but for $r = 0$ the utilization is the constant $t_2/(a+t_2)$ for $d > 0$ and none of items 1, 2, 4 holds. The value $\bar u(0)$ is computed as $0/0 = 0$ in Lean, which agrees with the paper's $\bar u(0) = 0$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 39, Lemma 2

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem lemma2_utilization (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) :
    StrictMonoOn (uBar P) (Set.Ici 0) ∧ StrictConcaveOn ℝ (Set.Ici 0) (uBar P) ∧
      uBar P 0 = 0 ∧ Filter.Tendsto (uBar P) Filter.atTop (nhds 1) := by sorry

end AVRideHail.PureHV
