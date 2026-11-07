-- Prove2me | Theorems.Thm_CloudCostOpt_eq_8_9_piHat_optimal
-- name    : CloudCostOpt.eq_8_9_piHat_optimal
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:11:30.10326+00:00
-- url     : https://prove2.me/theorems/03f200c6-2613-4fa9-ac39-78f38119b1ca
-- title:
--   (8)–(9) — $\hat\pi$ is optimal for $\mathbb P_{LB}$ and $LB=\sum_j R_j\mu_j+\sum_i\sum_{s\ge\delta_i}\sum_l W_i\lambda^x_i(s,l)$
-- statement:
--   The policy $\hat\pi$ is stable, its long-run average cost in the relaxed problem $\mathbb P_{LB}$ is
--
--   $$
--   f^{\hat\pi}_{LB}=\sum_{j=1}^{J}R_j\,\mu_j+\sum_{i=1}^{I}\sum_{s=\delta_i}^{\infty}\sum_{l=0}^{L_i-1}W_i\,\lambda^x_i(s,l),\qquad(8)
--   $$
--
--   and it attains the lower bound:
--
--   $$
--   LB=f^{\hat\pi}_{LB}.\qquad(9)
--   $$
--
--   Formula (8) is the closed form of the lower bound used to bound the optimality gap of $\pi^*$.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - reading: "number of" reserved and on-demand resources → capacities M_j, m_{j,t} ∈ [0, ∞) real; reason: the paper's own π* reserves µ_j + z_j√µ_j ∈ ℝ and rents (u − M)⁺ ∈ ℝ; real capacities only enlarge the policy class
--   - encoding: decisions depend on "every possible history until that period" and satisfy (1)–(2) → decisions are functions of the observed states x_1, …, x_t and satisfy (1)–(2) on every history; reason: past decisions are functions of past states, and off the reachable histories a decision can be replaced by idling; same policy class
--   - reading: f^π := lim_T (1/T) Σ_t E[C_t^π] → f^π := liminf_T (1/T) Σ_t E[C_t^π]; reason: the paper asserts the limit exists for stable policies, and then the two agree; otherwise liminf is smaller, so infima can only fall and the bounds only get stronger
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - reading: "π̂ is an optimal solution to Problem ℙ_LB" → π̂ ∈ Π, together with (8) and (9); reason: an optimal solution of ℙ_LB is a member of Π; stability is stated explicitly
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13 ("π̂, is an optimal solution to Problem P_LB"), p.15, (8)–(9)

import Mathlib
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`π̂` is optimal for `ℙ_LB`, (8) and (9)** (pp.13, 15): `π̂` is a stable policy; its cost in
`ℙ_LB` is
`f^π̂_LB = Σ_{j=1}^J R_j μ_j + Σ_{i=1}^I Σ_{s=δᵢ}^∞ Σ_{l=0}^{Lᵢ−1} Wᵢ λ^x_i(s, l)` (8);
and it attains the optimal cost, `LB = f^π̂_LB` (9).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13 ("ˆπ, is an optimal solution to Problem ℙ_LB"), p.15, (8)–(9). -/
theorem eq_8_9_piHat_optimal (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) :
    IsStable S lam (piHat S sel) ∧
    avgCost S S.R S.R lam (piHat S sel) =
      ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) ∧
    opt S S.R S.R lam = avgCost S S.R S.R lam (piHat S sel) := by sorry

end CloudCostOpt
