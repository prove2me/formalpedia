-- Prove2me | Theorems.Thm_CloudCostOpt_eq_11_piStar_cost
-- name    : CloudCostOpt.eq_11_piStar_cost
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:11:39.298567+00:00
-- url     : https://prove2.me/theorems/62212c25-b068-4f1b-bd1d-100d7ed31e89
-- title:
--   (11) — the long-run average cost of $\pi^*$
-- statement:
--   Assume $0<R_j<V_j$ (so that $z_j$ is finite) and $M_j=\mu_j+z_j\sqrt{\mu_j}\ge0$ for every $j$ (the paper's assumption of p.16). Then $\pi^*$ is stable and its long-run average expected cost is
--
--   $$
--   f^{\pi^*}=\sum_{j=1}^{J}R_j\big(\mu_j+z_j\sqrt{\mu_j}\big)+\sum_{j=1}^{J}V_j\,\mathbb E\Big[\big(U_j-(\mu_j+z_j\sqrt{\mu_j})\big)^+\Big]+\sum_{i=1}^{I}\sum_{s=\delta_i}^{\infty}\sum_{l=0}^{L_i-1}W_i\,\lambda^x_i(s,l),\qquad(11)
--   $$
--
--   where $U_j$ is a Poisson random variable with mean $\mu_j$.
--
--   The three terms are the reservation cost, the on-demand premium paid for usage above the reservation level, and the waiting cost, which $\pi^*$ shares with $\hat\pi$.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - encoding: 0 ≤ R_j ≤ V_j → 0 < R_j < V_j (hypotheses hR, hRV); reason: nondegeneracy condition: it excludes only the cases in which z_j = Φ⁻¹((V_j − R_j)/V_j) is ±∞ and π*, (14) are undefined
--   - reading: "number of" reserved and on-demand resources → capacities M_j, m_{j,t} ∈ [0, ∞) real; reason: the paper's own π* reserves µ_j + z_j√µ_j ∈ ℝ and rents (u − M)⁺ ∈ ℝ; real capacities only enlarge the policy class
--   - encoding: decisions depend on "every possible history until that period" and satisfy (1)–(2) → decisions are functions of the observed states x_1, …, x_t and satisfy (1)–(2) on every history; reason: past decisions are functions of past states, and off the reachable histories a decision can be replaced by idling; same policy class
--   - reading: f^π := lim_T (1/T) Σ_t E[C_t^π] → f^π := liminf_T (1/T) Σ_t E[C_t^π]; reason: the paper asserts the limit exists for stable policies, and then the two agree; otherwise liminf is smaller, so infima can only fall and the bounds only get stronger
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - encoding: M^{π*}_j := µ_j + z_j√µ_j under the assumption M^{π*}_j ≥ 0 → M^{π*}_j := (µ_j + z_j√µ_j)⁺, with the same assumption as a hypothesis; reason: the paper's own alternative definition (p.16); under the hypothesis the two coincide
--   - reading: f^{π*} is defined for π* ∈ Π → π* ∈ Π stated as a conclusion; reason: the formula (11) presupposes stability
--   - encoding: E[(U_j − Q)⁺] with U_j ~ Poisson(µ_j) → ∫⁻ k, (k − Q)⁺ d Poisson(µ_j); reason: Lean convention; same value
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §5, p.17, (11); p.16 (assumption M^{π*}_j ≥ 0)

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **(11)** (p.17): if `0 < R_j < V_j` (so that `z_j` is finite) and
`M^{π*}_j = μ_j + z_j √μ_j ≥ 0` for every `j` (the paper's standing assumption of p.16), then `π*`
is stable and its long-run average expected cost per period is
`f^{π*} = Σ_j R_j (μ_j + z_j √μ_j) + Σ_j V_j E[(U_j − (μ_j + z_j √μ_j))⁺]
  + Σ_{i=1}^I Σ_{s=δᵢ}^∞ Σ_{l=0}^{Lᵢ−1} Wᵢ λ^x_i(s, l)`, with `U_j ~ Poisson(μ_j)`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §5, p.17, (11); p.16 (assumption `M^{π*}_j ≥ 0`).

Formalization Note: `E[(U_j − Q)⁺] = ∫⁻ k, (k − Q)⁺ d Poisson(μ_j)`. -/
theorem eq_11_piStar_cost (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j)
    (hM : ∀ j, 0 ≤ (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) :
    IsStable S lam (piStar S sel lam) ∧
    avgCost S S.R S.V lam (piStar S sel lam) =
      ∑ j, ENNReal.ofReal
          (S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))) +
      ∑ j, ENNReal.ofReal (S.V j) * ∫⁻ k : ℕ,
          ENNReal.ofReal ((k : ℝ) -
            ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)))
          ∂(poissonMeasure (mu S sel lam j).toNNReal) +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) := by sorry

end CloudCostOpt
