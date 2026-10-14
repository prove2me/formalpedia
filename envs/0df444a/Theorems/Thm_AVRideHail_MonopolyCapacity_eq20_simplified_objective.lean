-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_eq20_simplified_objective
-- name    : AVRideHail.MonopolyCapacity.eq20_simplified_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:21.633821+00:00
-- url     : https://prove2.me/theorems/9bb0f424-c9cb-459c-bd28-12cfcb3f75a0
-- title:
--   (20), p. 29 — the monopoly objective (5) equals (w₀ − c_v) Σ P(m_i) min{N, n*_{HV,i}} − c_f N
-- statement:
--   Consider a common-platform market with $a > 0$, $0 < r < 1$, $t_2 > 0$, $V > 0$, constant HV reservation earnings $w_0$ ($\alpha = 0$), and AV costs $c_v, c_f > 0$ with $c_v + c_f < w_0$ (Assumption 1). There are $I \ge 1$ demand scenarios with potential demand masses $0 < m_1 < \dots < m_I$ and probabilities $P(m_i) \ge 0$ summing to $1$; every scenario is a loose market, with maximal stable pure-HV equilibrium demand $d^*_{HV,i}$ and fleet size $n^*_{HV,i} = \underline{n}(d^*_{HV,i})$. Then for every capacity $N \ge 0$ the monopoly objective (5) with the common-platform profit (251) equals
--   $$\sum_{i=1}^I P(m_i)\Big\{\max_{0 \le n_{AV,i} \le N} \pi^C_i(n_{AV,i})\, n_{AV,i}\Big\} - c_f N = (w_0 - c_v) \sum_{i=1}^I P(m_i) \min\{N, n^*_{HV,i}\} - c_f N.$$
--
--   This turns the capacity problem into a newsvendor problem with underage cost $w_0 - c_v$ and overage cost $c_f$.
--
--   **Formalization Note.** Scenarios are indexed by `Fin I` (0-based). The inner maximum of (5) is a real supremum over $[0, N]$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), pp. 28–29, (20), with (5) on p. 10

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem eq20_simplified_objective (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (halpha : P.alpha = 0)
    (cv cf : ℝ) (hcv : 0 < cv) (hcf : 0 < cf) (hA1 : cv + cf < P.w0)
    (I : ℕ) (hI : 0 < I) (prob : Fin I → ℝ) (hprob : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1)
    (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, AVRideHail.PureHV.LooseMarket P (m i))
    (dstar : Fin I → ℝ) (hdstar : ∀ i, AVRideHail.PureHV.IsMaxStableEq P (m i) (dstar i))
    (N : ℝ) (hN : 0 ≤ N) :
    monoProfit P cv cf prob m dstar N =
      profit20 P cv cf prob (fun i => AVRideHail.PureHV.nMin P (dstar i)) N := by sorry

end AVRideHail.MonopolyCapacity
