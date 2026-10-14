-- Prove2me | Theorems.Thm_AVRideHail_PureHV_proposition1_pure_hv_equilibrium
-- name    : AVRideHail.PureHV.proposition1_pure_hv_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:56.532397+00:00
-- url     : https://prove2.me/theorems/8fecbd32-b222-4294-98a3-0e458e466b40
-- title:
--   Proposition 1, p. 14 — unique maximal stable pure-HV equilibrium; d*, n*, u* increasing in m_i; p* = w(n*)/u*
-- statement:
--   Consider a pure human-driver ride-hailing market with ETA function $t_1(s) = a s^{-r}$, $a > 0$, $0 \le r < 1$, trip time $t_2 > 0$, rider values uniform on $[0, V]$ with $V > 0$, and HV reservation earnings $w(n) = w_0 + \alpha n$ with $w_0 > 0$, $\alpha \ge 0$. Consider $I$ demand scenarios with potential demand masses $0 < m_1 < m_2 < \dots < m_I$, and assume that each scenario is a loose labor market in the sense of (33): $r_i(m_i/2) > w(\underline{n}(m_i/2))\,\underline{n}(m_i/2)$, where $r_i(d) = d\,V(1-d/m_i)\,t_2$.
--
--   Then each scenario $i$ has a unique maximal stable equilibrium demand $d^*_{HV,i}$. Moreover, writing $n^*_{HV,i} = \underline{n}(d^*_{HV,i})$, $u^*_{HV,i} = \bar u(d^*_{HV,i})$ and $p^*_{HV,i} = V(1 - d^*_{HV,i}/m_i)$:
--
--   1. $d^*_{HV,i} > 0$ and
--   $$ r_i(d^*_{HV,i}) = w(n^*_{HV,i})\cdot n^*_{HV,i} \qquad (15),$$
--   and the equilibrium price is $p^*_{HV,i} = w(n^*_{HV,i})/u^*_{HV,i}$ (17);
--   2. $d^*_{HV,i}$ is strictly increasing in $i$;
--   3. if $r > 0$, the utilization $u^*_{HV,i}$ is strictly increasing in $i$; if $r = 0$, it is the same in every scenario;
--   4. the fleet size $n^*_{HV,i}$ is strictly increasing in $i$.
--
--   This is the paper's benchmark: in a market served only by human drivers, a denser market serves more demand, with a larger fleet and, when there is a density effect, a higher utilization. The markets with autonomous vehicles are compared against it.
--
--   **Formalization Note** The loose-market hypothesis (33) is not in the printed statement of Proposition 1; its proof (App. B.1.1, p. 42) restates Assumption 2 in this form and uses it, and without it a thin scenario has $d^* = 0$ and items 2–4 fail. It is the strict form of Assumption 2 (18). Scenarios are indexed by `Fin I`, 0-based: the paper's scenario $i$ is index $i-1$. Since a greatest element is unique, the content of "unique maximal stable equilibrium" is its existence; the remaining items are stated for any family `dstar` of maximal stable equilibria. "Increasing" is strict. Positivity of $d^*_{HV,i}$ is the paper's remark (p. 15) that under Assumption 2 HVs always provide service; it makes (17) meaningful. Item 5's remark that the price may be increasing, decreasing or non-monotonic is not posed; its two proved special cases are a separate milestone. Definition 1's $\epsilon$ is restricted to keep $d \pm \epsilon$ in $[0, m_i]$, the domain of the inverse demand.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 14, Proposition 1 (Items 1–4 and (17) of Item 5); p. 15, Assumption 2; proof App. B.1, pp. 42–46

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.PureHV

theorem proposition1_pure_hv_equilibrium (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (I : ℕ) (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, LooseMarket P (m i)) :
    (∀ i, ∃! d, IsMaxStableEq P (m i) d) ∧
      ∀ dstar : Fin I → ℝ, (∀ i, IsMaxStableEq P (m i) (dstar i)) →
        (∀ i, 0 < dstar i ∧ revenue P (m i) (dstar i) = hvCost P (dstar i) ∧
            priceFn P (m i) (dstar i) = wage P (nMin P (dstar i)) / uBar P (dstar i)) ∧
          StrictMono dstar ∧
          ((0 < P.r → StrictMono fun i => uBar P (dstar i)) ∧
            (P.r = 0 → ∀ i j, uBar P (dstar i) = uBar P (dstar j))) ∧
          StrictMono fun i => nMin P (dstar i) := by sorry

end AVRideHail.PureHV
