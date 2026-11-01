-- Prove2me | Theorems.Thm_CloudCostOpt_lb_le_opt
-- name    : CloudCostOpt.lb_le_opt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:11:30.108511+00:00
-- url     : https://prove2.me/theorems/1cd08830-88d8-4be4-ba89-9e313a127001
-- title:
--   p.11 — $OPT\ge LB$: replacing on-demand by reserved prices lowers the cost of every stable policy
-- statement:
--   For a stable policy $\pi$ let $f^\pi$ be its long-run average expected cost and $f^\pi_{LB}$ the same quantity with every on-demand price $V_j$ replaced by the reserved price $R_j\le V_j$. Then
--
--   $$
--   f^\pi_{LB}\le f^\pi\quad\text{for every }\pi\in\Pi,\qquad\text{hence}\qquad LB:=\inf_{\pi\in\Pi}f^\pi_{LB}\le\inf_{\pi\in\Pi}f^\pi=OPT.
--   $$
--
--   This is the first step of the paper's analysis: the relaxation $\mathbb P_{LB}$ bounds the firm's optimal cost from below.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - reading: "number of" reserved and on-demand resources → capacities M_j, m_{j,t} ∈ [0, ∞) real; reason: the paper's own π* reserves µ_j + z_j√µ_j ∈ ℝ and rents (u − M)⁺ ∈ ℝ; real capacities only enlarge the policy class
--   - encoding: decisions depend on "every possible history until that period" and satisfy (1)–(2) → decisions are functions of the observed states x_1, …, x_t and satisfy (1)–(2) on every history; reason: past decisions are functions of past states, and off the reachable histories a decision can be replaced by idling; same policy class
--   - reading: f^π := lim_T (1/T) Σ_t E[C_t^π] → f^π := liminf_T (1/T) Σ_t E[C_t^π]; reason: the paper asserts the limit exists for stable policies, and then the two agree; otherwise liminf is smaller, so infima can only fall and the bounds only get stronger
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.11

import Mathlib
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`OPT ≥ LB`** (§3, p.11): for every stable policy `π`, `f^π_LB ≤ f^π` (the on-demand price
`V_j` replaced by `R_j ≤ V_j`), hence `LB = inf_{π∈Π} f^π_LB ≤ inf_{π∈Π} f^π = OPT`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.11.

Formalization Note: `f^π_LB = avgCost S S.R S.R lam π`, `f^π = avgCost S S.R S.V lam π`. -/
theorem lb_le_opt (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) :
    (∀ π : Policy S, IsStable S lam π → avgCost S S.R S.R lam π ≤ avgCost S S.R S.V lam π) ∧
    opt S S.R S.R lam ≤ opt S S.R S.V lam := by sorry

end CloudCostOpt
