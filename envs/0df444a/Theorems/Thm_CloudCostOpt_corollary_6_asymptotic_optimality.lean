-- Prove2me | Theorems.Thm_CloudCostOpt_corollary_6_asymptotic_optimality
-- name    : CloudCostOpt.corollary_6_asymptotic_optimality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:12:44.796411+00:00
-- url     : https://prove2.me/theorems/ad0aeda3-4c89-417a-8ab7-c4cd4f522088
-- title:
--   Corollary 6 — $\pi^*$ is asymptotically optimal as demand scales by $\theta$ (corrected: Δ(θ) ≤ √θ·B(1))
-- statement:
--   Scale the vector of demand rates by $\theta\ge0$ (replace $\lambda$ by $\theta\lambda$, nothing else changes), and write $LB(\theta)$, $OPT(\theta)$ and $f^{\pi^*}(\theta)$ for the lower bound, the optimal value and the cost of the policy $\pi^*$ in the scaled problem. Let
--
--   $$
--   B(1)=\sum_{j=1}^{J}\Big(R_jz_j+V_j\,\frac{\sqrt{1+z_j^2}-z_j}{2}\Big)\sqrt{\mu_j(1)},
--   $$
--
--   the right side of (14) at $\theta=1$. Then, for every instance satisfying the standing assumptions and $0<R_j<V_j$ (so that every $z_j$ is finite), and every selection $j^*$ of optimal resources:
--
--   1. $LB(\theta)=\theta\cdot LB(1)$ for every $\theta\ge0$, and $0<LB(1)<\infty$;
--   2. for every $\theta\ge0$, $\pi^*(\theta)$ is a stable policy with $f^{\pi^*}(\theta)<\infty$;
--   3. for every $\theta\ge0$ with $\mu_j(\theta)+z_j\sqrt{\mu_j(\theta)}\ge0$ for all $j$: $LB(\theta)\le OPT(\theta)\le f^{\pi^*}(\theta)$,
--
--   $$
--   \Delta^{\pi^*}(\theta)=f^{\pi^*}(\theta)-LB(\theta)\le\sqrt\theta\,B(1),
--   $$
--
--   and, if moreover $\theta>0$,
--
--   $$
--   \frac{f^{\pi^*}(\theta)-OPT(\theta)}{OPT(\theta)}\le\frac{\Delta^{\pi^*}(\theta)}{OPT(\theta)}\le\frac{\Delta^{\pi^*}(\theta)}{LB(\theta)}\le\frac{B(1)}{LB(1)\sqrt\theta};
--   $$
--
--   4. as $\theta\to\infty$, the relative gaps $(f^{\pi^*}(\theta)-OPT(\theta))/OPT(\theta)$, $\Delta^{\pi^*}(\theta)/OPT(\theta)$ and $\Delta^{\pi^*}(\theta)/LB(\theta)$ converge to $0$: $\pi^*$ is asymptotically optimal, with relative optimality gap $O(1/\sqrt\theta)$.
--
--   This is the paper's headline: a simple policy built from the per-order dynamic programs and a normal newsvendor reservation level is asymptotically optimal for the coupled problem.
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
--   - correction: Δ^{π*}(θ) = √θ · Δ^{π*}(1) → Δ^{π*}(θ) ≤ √θ · B(1), B(1) the right side of (14) at θ = 1; reason: the printed equality is false: for I = J = 1, L = δ = β_{1,1} = λ = W = R = 1, V = 2 (all assumptions hold, M ≥ 0), Δ(θ) = 2E[(Poisson(θ) − θ)⁺], so Δ(1) = 2/e ≈ 0.7358 and Δ(4) ≈ 1.5629 ≠ 2Δ(1) ≈ 1.4715; the bound is the paper's own sentence before the corollary
--   - generalization: π* with M_j = µ_j + z_j√µ_j under the standing assumption M_j ≥ 0 (p.16) → π* with M_j = (µ_j + z_j√µ_j)⁺; the bounds of clause 3 keep M_j ≥ 0 as a hypothesis, clauses 2 and 4 hold without it; reason: the paper's own alternative definition (p.16); where M_j ≥ 0 the two agree, and M_j(θ) ≥ 0 holds for all large θ, so the statement specializes to the paper's
--   - encoding: θ ≥ 0 real → θ : ℝ≥0; reason: Lean convention; same values
--   - encoding: Δ^{π*} = f^{π*} − LB as a real number → f^{π*}, LB ∈ [0, ∞] shown finite, Δ = (f^{π*}).toReal − LB.toReal; reason: the finiteness clauses make toReal faithful; no truncated subtraction
--   - encoding: the ratios Δ/OPT, Δ/LB for θ ≥ 0, and θ → ∞ in the limit → real ratios of toReal values, formed after finiteness and positivity are stated, for θ > 0; reason: no division by zero or truncated subtraction can make a clause vacuous; at θ = 0 the costs vanish and no ratio exists
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Corollary 6, p.18, with (14), p.17

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Corollary 6, with the bound (14)** (pp.17–18), corrected.  Scale the arrival rates by
`θ ≥ 0` (`λ ↦ θλ`, nothing else changes) and write `LB(θ)`, `OPT(θ)`, `f^{π*}(θ)` for the
lower bound, the optimal value and the cost of `π*` in the scaled problem, and
`B(1) := Σ_j (R_j z_j + V_j(√(1 + z_j²) − z_j)/2) √μ_j(1)`, the right side of (14) at `θ = 1`.
Assume `0 < R_j < V_j`, so that every `z_j` is finite.  Then
1. `LB(θ) = θ · LB(1)` for every `θ ≥ 0`, and `0 < LB(1) < ∞`;
2. for every `θ ≥ 0`, `π*(θ)` is a stable policy and `f^{π*}(θ) < ∞`;
3. for every `θ ≥ 0` with `M^{π*}_j(θ) = μ_j(θ) + z_j √μ_j(θ) ≥ 0` for all `j`:
   `LB(θ) ≤ OPT(θ) ≤ f^{π*}(θ)` and `Δ^{π*}(θ) := f^{π*}(θ) − LB(θ) ≤ √θ · B(1)`; if moreover
   `θ > 0`, then
   `(f^{π*} − OPT)/OPT ≤ Δ^{π*}(θ)/OPT(θ) ≤ Δ^{π*}(θ)/LB(θ) ≤ B(1)/(LB(1)√θ)`;
4. as `θ → ∞`, `(f^{π*} − OPT)/OPT → 0`, `Δ^{π*}(θ)/OPT(θ) → 0` and `Δ^{π*}(θ)/LB(θ) → 0`:
   `π*` is asymptotically optimal.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Corollary 6, p.18, with (14), p.17.

Formalization Notes:
* the printed clause `Δ^{π*}(θ) = √θ · Δ^{π*}(1)` is false and is replaced by `Δ^{π*}(θ) ≤ √θ·B(1)`
  (the paper's own sentence before the corollary: "the upper bound on `Δ^{π*}` scales proportionally
  to `√θ`");
* `π*` is defined with `M_j = (μ_j + z_j√μ_j)⁺`; clause 3 keeps the paper's assumption `M_j ≥ 0`,
  clauses 2 and 4 hold without it;
* ratios are real numbers, formed after clauses 1–3 establish finiteness and positivity; at
  `θ = 0` the costs vanish and no ratio exists. -/
theorem corollary_6_asymptotic_optimality (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j) :
    let LB : ℝ≥0 → ℝ≥0∞ := fun θ => opt S S.R S.R (θ • lam)
    let OPT : ℝ≥0 → ℝ≥0∞ := fun θ => opt S S.R S.V (θ • lam)
    let fStar : ℝ≥0 → ℝ≥0∞ := fun θ => avgCost S S.R S.V (θ • lam) (piStar S sel (θ • lam))
    let B1 : ℝ := ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
      √((mu S sel lam j).toReal)
    -- 1. scaling of the lower bound, and `0 < LB(1) < ∞`
    (∀ θ : ℝ≥0, LB θ = (θ : ℝ≥0∞) * LB 1) ∧ 0 < LB 1 ∧ LB 1 < ⊤ ∧
    -- 2. `π*(θ)` is stable, with finite cost
    (∀ θ : ℝ≥0, IsStable S (θ • lam) (piStar S sel (θ • lam)) ∧ fStar θ < ⊤) ∧
    -- 3. the bounds, under `M^{π*}_j(θ) ≥ 0`
    (∀ θ : ℝ≥0,
      (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      LB θ ≤ OPT θ ∧ OPT θ ≤ fStar θ ∧
      (fStar θ).toReal - (LB θ).toReal ≤ √(θ : ℝ) * B1) ∧
    (∀ θ : ℝ≥0, 0 < θ →
      (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ≤
        B1 / ((LB 1).toReal * √(θ : ℝ))) ∧
    -- 4. asymptotic optimality
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal)
      atTop (𝓝 0) ∧
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal)
      atTop (𝓝 0) ∧
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal)
      atTop (𝓝 0) := by sorry

end CloudCostOpt
