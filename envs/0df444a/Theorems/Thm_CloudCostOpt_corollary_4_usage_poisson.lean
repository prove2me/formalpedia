-- Prove2me | Theorems.Thm_CloudCostOpt_corollary_4_usage_poisson
-- name    : CloudCostOpt.corollary_4_usage_poisson
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:10:26.122405+00:00
-- url     : https://prove2.me/theorems/cdeb0e97-983b-4095-a214-d51e66a461d7
-- title:
--   Corollary 4 — the usage $u^{\hat\pi}_{j,t}$ is Poisson, with mean and variance tending to $\mu_j$
-- statement:
--   Under $\hat\pi$, for every real resource type $1\le j\le J$ and every period $t\ge1$, the number $u_{j,t}$ of type-$j$ resources used in period $t$ is a Poisson random variable with mean (equal to its variance)
--
--   $$
--   \mathbb E[u_{j,t}]=\sum_{i=1}^{I}\sum_{s=0}^{t-2}\ \sum_{l=0,\ j^*(i,s,l)=j}^{\min(L_i-1,s)}\lambda^x_i(s,l).
--   $$
--
--   As $t\to\infty$, the expectation and the variance of $u_{j,t}$ converge to $\mu_j$:
--
--   $$
--   \lim_{t\to\infty}\mathbb E[u_{j,t}]=\lim_{t\to\infty}\operatorname{Var}(u_{j,t})=\mu_j.
--   $$
--
--   This is the fact behind the newsvendor choice of $\pi^*$: the eventual demand for type-$j$ resources is Poisson with mean and variance $\mu_j$.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - encoding: variance Var(u_{j,t}) → evariance (variance in [0, ∞]) of the real-valued u_{j,t}; reason: Lean convention; no junk 0 for a variable of infinite variance
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Corollary 4, p.15

import Mathlib
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_stateAt
import Definitions.Def_CloudCostOpt_sampleMeasure
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Corollary 4** (p.15): for every `1 ≤ j ≤ J` and every `t ≥ 1`, `u^π̂_{j,t}` is a Poisson
random variable with mean (which equals its variance)
`E[u^π̂_{j,t}] = Σ_{i=1}^I Σ_{s=0}^{t−2} Σ_{l=0, j*(i,s,l)=j}^{min(Lᵢ−1,s)} λ^x_i(s, l)`;
as `t → ∞` the expectation and the variance of `u^π̂_{j,t}` approach `μ_j`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Corollary 4, p.15.

Formalization Note: `u^π̂_{j,t} = usage … (t − 1) x_t j`, the on-demand capacity of `π̂` in period
`t`. -/
theorem corollary_4_usage_poisson (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) (j : Fin S.J) :
    let P := sampleMeasure S lam
    let u : ℕ → Omega S → ℕ := fun t ω =>
      usage S sel (t - 1) (stateAt S (piHat S sel) ω (t - 1)) j
    let ν : ℕ → ℝ≥0 := fun t => ∑ i, ∑ s ∈ Finset.range (t - 1),
      ∑ l ∈ Finset.range (min (S.L i - 1) s + 1),
        if sel.jStar i s l = j.succ then rateX S sel lam i s l else 0
    (∀ t, 1 ≤ t →
      HasLaw (u t) (poissonMeasure (ν t)) P ∧
      ∫⁻ ω, (u t ω : ℝ≥0∞) ∂P = ν t ∧
      evariance (fun ω => (u t ω : ℝ)) P = ν t) ∧
    Tendsto (fun t => ∫⁻ ω, (u t ω : ℝ≥0∞) ∂P) atTop (𝓝 (mu S sel lam j)) ∧
    Tendsto (fun t => evariance (fun ω => (u t ω : ℝ)) P) atTop (𝓝 (mu S sel lam j)) := by sorry

end CloudCostOpt
