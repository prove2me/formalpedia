-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_proposition8_optimal_capacity
-- name    : AVRideHail.MonopolyCapacity.proposition8_optimal_capacity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:46.132564+00:00
-- url     : https://prove2.me/theorems/c148082b-7e84-4cef-ab71-5b2d8c32b3df
-- title:
--   Proposition 8, p. 29 — the monopoly's optimal AV capacity is N* = n*_{HV,K}, K the smallest i with Σ_{K+1}^I P(m_i) < c_f/(w₀ − c_v)
-- statement:
--   Consider a ride-hailing market in which a monopoly supplier of autonomous vehicles (AVs) and human drivers (HVs) operate on a common platform. The market has pickup-time function $t_1(s) = a s^{-r}$ with $a > 0$ and $0 < r < 1$, trip time $t_2 > 0$, maximal rider value $V > 0$, and perfectly elastic HV supply at reservation earnings $w_0$ ($\alpha = 0$). AVs cost $c_v > 0$ per operating hour and $c_f > 0$ per calendar hour, with $c_v + c_f < w_0$ (Assumption 1).
--
--   Demand is random with $I \ge 1$ scenarios: potential demand masses $0 < m_1 < m_2 < \dots < m_I$ with probabilities $P(m_i) \ge 0$, $\sum_i P(m_i) = 1$. Each scenario is a loose market (condition (33)); $d^*_{HV,i}$ is its maximal stable pure-HV equilibrium demand and $n^*_{HV,i} = \underline{n}(d^*_{HV,i})$ the pure-HV equilibrium fleet size. The supplier first fixes a capacity $N \ge 0$ and then, in each scenario, a fleet $n_{AV,i} \in [0, N]$, maximizing (5):
--   $$\max_{N \ge 0} \; \sum_{i=1}^I P(m_i) \Big\{\max_{0 \le n_{AV,i} \le N} \pi^C_i(n_{AV,i})\, n_{AV,i}\Big\} - c_f N,$$
--   where $\pi^C_i$ is the common-platform variable profit per AV (251).
--
--   Let $K$ be the smallest index $i$ such that $\sum_{j=i+1}^I P(m_j) < c_f/(w_0 - c_v)$. Then
--   $$N^* = n^*_{HV,K}$$
--   is an optimal capacity for (5).
--
--   The result says the monopoly's capacity problem is a newsvendor problem: the optimal capacity is the pure-HV fleet size of the scenario at the critical fractile $c_f/(w_0 - c_v)$ of the demand distribution.
--
--   **Formalization Note.** Scenarios are indexed by `Fin I`, from $0$ to $I - 1$; the page's $\sum_{K+1}^I$ is the sum over indices strictly above $K$, and "the smallest $i$" is `IsLeast`. The page's "in a loose market" is the loose-market condition (33) in every scenario. The conclusion is that $n^*_{HV,K}$ maximizes (5) over $N \ge 0$, not that it is the unique maximizer: when $\sum_{j \ge K} P(m_j) = c_f/(w_0 - c_v)$ exactly, the objective takes the same value at $n^*_{HV,K-1}$, so the page's "the optimal AV capacity" is one of the optima. The variable profit $\pi^C_i$ is the paper's summary (251) of Proposition 6, taken as a definition.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 29, Proposition 8, (21); proof App. E.1.3, pp. 86–88

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem proposition8_optimal_capacity (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (halpha : P.alpha = 0)
    (cv cf : ℝ) (hcv : 0 < cv) (hcf : 0 < cf) (hA1 : cv + cf < P.w0)
    (I : ℕ) (hI : 0 < I) (prob : Fin I → ℝ) (hprob : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1)
    (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, AVRideHail.PureHV.LooseMarket P (m i))
    (dstar : Fin I → ℝ) (hdstar : ∀ i, AVRideHail.PureHV.IsMaxStableEq P (m i) (dstar i))
    (K : Fin I) (hK : IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < cf / (P.w0 - cv)} K) :
    IsMaxOn (monoProfit P cv cf prob m dstar) (Set.Ici 0) (AVRideHail.PureHV.nMin P (dstar K)) := by sorry

end AVRideHail.MonopolyCapacity
