-- Prove2me | Theorems.Thm_CloudCostOpt_eq_10_lb_order_values
-- name    : CloudCostOpt.eq_10_lb_order_values
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:11:25.077027+00:00
-- url     : https://prove2.me/theorems/db06fae3-e925-46f5-b861-f164f0c11595
-- title:
--   (10) — $LB=\sum_i\lambda_i f_i(0,0)$
-- statement:
--   The lower bound equals the arrival-rate-weighted sum of the optimal values of the single-order problems:
--
--   $$
--   LB=\sum_{i=1}^{I}\lambda_i\,f_i(0,0),\qquad(10)
--   $$
--
--   where $f_i(0,0)$ is the optimal value of $\hat{\mathbb P}_i$ for a newly arrived type-$i$ order.
--
--   This expression makes the linear scaling of $LB$ in the demand rates visible, which is used in Corollary 6.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - reading: "number of" reserved and on-demand resources → capacities M_j, m_{j,t} ∈ [0, ∞) real; reason: the paper's own π* reserves µ_j + z_j√µ_j ∈ ℝ and rents (u − M)⁺ ∈ ℝ; real capacities only enlarge the policy class
--   - encoding: decisions depend on "every possible history until that period" and satisfy (1)–(2) → decisions are functions of the observed states x_1, …, x_t and satisfy (1)–(2) on every history; reason: past decisions are functions of past states, and off the reachable histories a decision can be replaced by idling; same policy class
--   - reading: f^π := lim_T (1/T) Σ_t E[C_t^π] → f^π := liminf_T (1/T) Σ_t E[C_t^π]; reason: the paper asserts the limit exists for stable policies, and then the two agree; otherwise liminf is smaller, so infima can only fall and the bounds only get stronger
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - encoding: the minimum expected remaining cost over all ways of processing the order → infimum over deterministic strategies that are functions of the past step outcomes, with i.i.d. uniform step trials; reason: Lean convention for the single-order control problem; the outcome history is all the controller observes
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.15, (10)

import Mathlib
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_orderValue
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **(10)** (p.15): `LB = Σ_{i=1}^I λᵢ · fᵢ(0, 0)`, where `fᵢ(0, 0)` is the optimal value of the
single-order problem `ℙ̂ᵢ` from order-state `(0, 0)`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.15, (10). -/
theorem eq_10_lb_order_values (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0)
    (hlam : ∀ i, 0 < lam i) :
    opt S S.R S.R lam = ∑ i, (lam i : ℝ≥0∞) * orderValue S i 0 0 := by sorry

end CloudCostOpt
