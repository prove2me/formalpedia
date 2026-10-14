-- Prove2me | Theorems.Thm_AVRideHail_PureHV_b11_unique_root_is_max_stable
-- name    : AVRideHail.PureHV.b11_unique_root_is_max_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:46.975918+00:00
-- url     : https://prove2.me/theorems/0e2eee2a-3ec6-4e2c-af9f-c96e25125c8f
-- title:
--   App. B.1.1, pp. 42–43 — under (33), (13) has exactly one root in [m/2, m]; it lies in (m/2, m) and is the maximal stable equilibrium
-- statement:
--   Consider a pure-HV market with parameters $a > 0$, $0 \le r < 1$, $t_2 > 0$, $V > 0$, $w_0 > 0$, $\alpha \ge 0$ and a demand scenario with potential demand mass $m > 0$, revenue $r(d) = d\,V(1 - d/m)\,t_2$ and minimal driver cost $C(d) = w(\underline{n}(d))\,\underline{n}(d)$. Assume the loose labor market condition
--   $$ r(m/2) > w(\underline{n}(m/2))\,\underline{n}(m/2) \qquad (33).$$
--   Then there is a demand rate $d$ with $m/2 < d < m$ that is the maximal stable equilibrium of the scenario, and it is the only $d' \in [m/2, m]$ satisfying the equilibrium condition $r(d') = C(d')$.
--
--   This is the existence-and-uniqueness step of Proposition 1: it locates the maximal stable equilibrium on the decreasing branch of the revenue curve.
--
--   **Formalization Note** "Maximal stable equilibrium" is `IsMaxStableEq` of the Model file: the greatest demand rate in $[0,m]$ that satisfies (13) and Definition 1 (with $\epsilon$ restricted so that $d \pm \epsilon \in [0,m]$). Positivity of $a, t_2, V$ and $w_0$ is the paper's reading of its parameters (pp. 7–9).
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), App. B.1.1, pp. 42–43, (33)–(38)

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem b11_unique_root_is_max_stable (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (m : ℝ) (hm : 0 < m) (hloose : LooseMarket P m) :
    ∃ d, m / 2 < d ∧ d < m ∧ IsMaxStableEq P m d ∧
      ∀ d' ∈ Set.Icc (m / 2) m, revenue P m d' = hvCost P d' → d' = d := by sorry

end AVRideHail.PureHV
