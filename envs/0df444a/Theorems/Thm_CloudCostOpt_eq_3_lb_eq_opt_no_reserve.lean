-- Prove2me | Theorems.Thm_CloudCostOpt_eq_3_lb_eq_opt_no_reserve
-- name    : CloudCostOpt.eq_3_lb_eq_opt_no_reserve
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:12:30.990774+00:00
-- url     : https://prove2.me/theorems/62639eb5-2ae1-4862-98ab-1e6de77b9173
-- title:
--   (3) — $LB=OPT(\infty,\mathbf R)$: in $\mathbb P_{LB}$ it is optimal to reserve nothing
-- statement:
--   In the relaxed problem $\mathbb P_{LB}=\mathbb P(\mathbf R,\mathbf R)$ the on-demand price of every resource type equals its reserved price, so reserving resources never helps:
--
--   $$
--   LB=OPT(\infty,\mathbf R),
--   $$
--
--   where $OPT(\infty,\mathbf R)$ is the infimum of $f^\pi_{LB}$ over the stable policies with $M_j=0$ for all $j$.
--
--   This identifies $\mathbb P_{LB}$ with a problem in which resources are hired one period at a time, which then decomposes order by order.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - reading: "number of" reserved and on-demand resources → capacities M_j, m_{j,t} ∈ [0, ∞) real; reason: the paper's own π* reserves µ_j + z_j√µ_j ∈ ℝ and rents (u − M)⁺ ∈ ℝ; real capacities only enlarge the policy class
--   - encoding: decisions depend on "every possible history until that period" and satisfy (1)–(2) → decisions are functions of the observed states x_1, …, x_t and satisfy (1)–(2) on every history; reason: past decisions are functions of past states, and off the reachable histories a decision can be replaced by idling; same policy class
--   - reading: f^π := lim_T (1/T) Σ_t E[C_t^π] → f^π := liminf_T (1/T) Σ_t E[C_t^π]; reason: the paper asserts the limit exists for stable policies, and then the two agree; otherwise liminf is smaller, so infima can only fall and the bounds only get stronger
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - encoding: ℙ(∞, R): reserved resources infinitely expensive → infimum over stable policies with M = 0; reason: a policy with some M_j > 0 costs +∞ per period in ℙ(∞, R), so only M = 0 matters
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.12, (3)

import Mathlib
import Definitions.Def_CloudCostOpt_optNoReserve
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **(3): `LB = OPT(∞, R)`** (§3, p.12): in `ℙ_LB` the on-demand price equals the reserved price,
so it is optimal to reserve nothing; the optimal value of `ℙ_LB` equals that of `ℙ(∞, R)`, the
infimum of `f^π_LB` over stable policies with `M = 0`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.12, (3). -/
theorem eq_3_lb_eq_opt_no_reserve (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0)
    (hlam : ∀ i, 0 < lam i) :
    opt S S.R S.R lam = optNoReserve S lam := by sorry

end CloudCostOpt
