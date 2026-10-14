-- Prove2me | Theorems.Thm_AVRideHail_PureHV_b16_price_special_cases
-- name    : AVRideHail.PureHV.b16_price_special_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:48.714778+00:00
-- url     : https://prove2.me/theorems/84a02ee2-fb1b-4a26-909c-1aa201859f37
-- title:
--   App. B.1.6, pp. 45–46 — equilibrium price increasing in m_i when r = 0, α > 0; decreasing when r > 0, α = 0
-- statement:
--   Consider a pure-HV market with parameters $a > 0$, $0 \le r < 1$, $t_2 > 0$, $V > 0$, $w_0 > 0$, $\alpha \ge 0$, and $I$ demand scenarios with potential demand masses $0 < m_1 < m_2 < \dots < m_I$, each satisfying the loose labor market condition (33). Let $d^*_{HV,i}$ be the maximal stable equilibrium demand of scenario $i$ and $p^*_{HV,i} = V(1 - d^*_{HV,i}/m_i)$ the equilibrium price. Then:
--
--   1. if $\alpha > 0$ and $r = 0$ (finite supply elasticity, no density effect), $p^*_{HV,i}$ is strictly increasing in $i$;
--   2. if $\alpha = 0$ and $r > 0$ (perfect supply elasticity, density effect), $p^*_{HV,i}$ is strictly decreasing in $i$.
--
--   $$ \alpha > 0,\ r = 0 \implies p^*_{HV,1} < \dots < p^*_{HV,I}, \qquad \alpha = 0,\ r > 0 \implies p^*_{HV,1} > \dots > p^*_{HV,I}. $$
--
--   These two cases show that the price in Item 5 of Proposition 1 can move in either direction, depending on whether the supply effect of labor or the density effect dominates.
--
--   **Formalization Note** Scenarios are indexed by `Fin I`, 0-based: the paper's scenario $i$ is index $i-1$. The maximal stable equilibria are taken as given functions `dstar` with `IsMaxStableEq` in each scenario, not chosen; the price is the inverse demand (3) at $d^*_{HV,i}$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. B.1.6, pp. 45–46, (47) and the two special cases

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem b16_price_special_cases (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (I : ℕ) (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, LooseMarket P (m i)) (dstar : Fin I → ℝ)
    (hdstar : ∀ i, IsMaxStableEq P (m i) (dstar i)) :
    (0 < P.alpha → P.r = 0 → StrictMono fun i => priceFn P (m i) (dstar i)) ∧
      (P.alpha = 0 → 0 < P.r → StrictAnti fun i => priceFn P (m i) (dstar i)) := by sorry

end AVRideHail.PureHV
