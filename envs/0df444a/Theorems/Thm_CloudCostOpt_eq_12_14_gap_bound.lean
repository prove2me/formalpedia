-- Prove2me | Theorems.Thm_CloudCostOpt_eq_12_14_gap_bound
-- name    : CloudCostOpt.eq_12_14_gap_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:12:35.862285+00:00
-- url     : https://prove2.me/theorems/87d1e33a-cc62-44c6-a718-097d01c77a09
-- title:
--   (12) and (14) — the optimality gap of $\pi^*$ and its bound
-- statement:
--   Assume $0<R_j<V_j$ (so that $z_j$ is finite) and $\mu_j+z_j\sqrt{\mu_j}\ge0$ for every $j$. Then $f^{\pi^*}$, $LB$ and $OPT$ are finite, and the gap $\Delta^{\pi^*}=f^{\pi^*}-LB\ge f^{\pi^*}-OPT$ satisfies
--
--   $$
--   \Delta^{\pi^*}=\sum_{j=1}^{J}\Big(R_jz_j\sqrt{\mu_j}+V_j\,\mathbb E\big[(U_j-(\mu_j+z_j\sqrt{\mu_j}))^+\big]\Big)\qquad(12)
--   $$
--
--   and
--
--   $$
--   \Delta^{\pi^*}\le\sum_{j=1}^{J}\Big(R_jz_j\sqrt{\mu_j}+V_j\,\frac{\sqrt{\mu_j(1+z_j^2)}-z_j\sqrt{\mu_j}}{2}\Big)=\sum_{j=1}^{J}\Big(R_jz_j+V_j\,\frac{\sqrt{1+z_j^2}-z_j}{2}\Big)\sqrt{\mu_j},\qquad(14)
--   $$
--
--   where $U_j\sim\mathrm{Poisson}(\mu_j)$.
--
--   The bound (14) is of order $\sqrt{\mu_j}$, while $LB$ is of order $\mu_j$; this is the source of the asymptotic optimality of $\pi^*$.
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
--   - encoding: E[(U_j − Q)⁺] with U_j ~ Poisson(µ_j) → ∫⁻ k, (k − Q)⁺ d Poisson(µ_j); reason: Lean convention; same value
--   - encoding: Δ^{π*} = f^{π*} − LB as a real number → f^{π*}, LB, OPT ∈ [0, ∞] shown finite, Δ = (f^{π*}).toReal − LB.toReal; reason: the finiteness clauses make toReal faithful; no truncated subtraction
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §5, p.17, (12), (14)

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **(12) and (14)** (p.17): if `0 < R_j < V_j` (so that `z_j` is finite) and
`M^{π*}_j = μ_j + z_j √μ_j ≥ 0` for every `j`, then `f^{π*}`, `LB` and `OPT` are finite and
`Δ^{π*} := f^{π*} − LB` satisfies `Δ^{π*} ≥ f^{π*} − OPT`,
`Δ^{π*} = Σ_j (R_j z_j √μ_j + V_j E[(U_j − (μ_j + z_j √μ_j))⁺])` (12), and
`Δ^{π*} ≤ Σ_j (R_j z_j √μ_j + V_j (√(μ_j(1 + z_j²)) − z_j √μ_j)/2)
  = Σ_j (R_j z_j + V_j (√(1 + z_j²) − z_j)/2) √μ_j` (14),
with `U_j ~ Poisson(μ_j)`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §5, p.17, (12), (14).

Formalization Note: `Δ^{π*}` is computed in `ℝ` after the finiteness clauses; both lines of (14)
are stated, the second as an equality with the first. -/
theorem eq_12_14_gap_bound (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j)
    (hM : ∀ j, 0 ≤ (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) :
    let μr : Fin S.J → ℝ := fun j => (mu S sel lam j).toReal
    let Δ : ℝ := (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.R lam).toReal
    avgCost S S.R S.V lam (piStar S sel lam) ≠ ⊤ ∧ opt S S.R S.R lam ≠ ⊤ ∧
    opt S S.R S.V lam ≠ ⊤ ∧
    (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.V lam).toReal ≤ Δ ∧
    Δ = ∑ j, (S.R j * zCoef S j * √(μr j) + S.V j *
      (∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - (μr j + zCoef S j * √(μr j)))
        ∂(poissonMeasure (mu S sel lam j).toNNReal)).toReal) ∧
    Δ ≤ ∑ j, (S.R j * zCoef S j * √(μr j) +
      S.V j * (√(μr j * (1 + zCoef S j ^ 2)) - zCoef S j * √(μr j)) / 2) ∧
    ∑ j, (S.R j * zCoef S j * √(μr j) +
        S.V j * (√(μr j * (1 + zCoef S j ^ 2)) - zCoef S j * √(μr j)) / 2) =
      ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
        √(μr j) := by sorry

end CloudCostOpt
