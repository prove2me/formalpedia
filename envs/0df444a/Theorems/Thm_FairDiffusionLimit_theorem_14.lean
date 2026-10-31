-- Prove2me | Theorems.Thm_FairDiffusionLimit_theorem_14
-- name    : FairDiffusionLimit.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:44.945006+00:00
-- url     : https://prove2.me/theorems/7862d472-8f00-4be8-ab55-44bbfa6e83cb
-- title:
--   Theorem 14 — interchange of limits: $\hat\pi^k_1\Rightarrow\hat\pi_1$ and convergence of moments of order $m<p-1$
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17). Assume the usual traffic condition $A\theta<0$ (66) and the bounded workload condition (71):
--   $$\sup_{0\le s\le t}|\hat W^k(s)|\le\kappa\Big(|\hat W^k(0)|+\sup_{0\le s\le t}|\hat X^k(s)|\Big)\quad\text{for all }k,\ t\ge0\text{ and every sample path.}$$
--   Then there is $k_0$ such that
--
--   1. every network $k\ge k_0$ has a stationary distribution;
--   2. the diffusion limit $\hat W$ has a stationary distribution $\hat\pi_1$, and no other;
--   3. for every choice of stationary distributions $\pi^k$ ($k\ge k_0$), the laws $\hat\pi^k_1$ of $\hat W^k(0)=W^k(0)/k$ under $\pi^k$ converge weakly:
--   $$\hat\pi^k_1\Rightarrow\hat\pi_1\qquad(k\to\infty);\tag{79}$$
--   4. for every real $m\in[0,p-1)$, $E_{\hat\pi_1}|\hat W(0)|^m<\infty$ and
--   $$E_{\hat\pi^k_1}|\hat W^k(0)|^m\to E_{\hat\pi_1}|\hat W(0)|^m\qquad(k\to\infty).\tag{80}$$
--
--   So the limits $t\to\infty$ and $k\to\infty$ can be interchanged: the stationary law of the diffusion limit approximates the stationary workload of the heavily loaded PF network, including its moments of order below $p-1$.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). Weak convergence is convergence in the space of probability measures on $\mathbb R^R$; moments are lower Lebesgue integrals in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: (15): nonnegative p(x) with ∫₀^∞ p(s) > 0; P{a ≤ ∑_{i=2}^j u^k_r(i) ≤ b} ≥ ∫_a^b p → p measurable; the law of the sum is the image of the product law under the sum of the first j − 1 coordinates; reason: measurability is needed for ∫ p to be defined; the sum of j − 1 i.i.d. copies has exactly that law
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
--   - encoding: X̂ a Brownian motion with drift θ and covariance Υ (p.13) → published Reiman84.QueueLength.IsDriftedBM θ Υ: X̂(0) = 0, every path continuous, independent Gaussian increments; reason: X̂(0) = 0 is forced by (24); continuity of every path instead of almost every path changes no law
--   - reading: "where Ŵ(0) ∈ 𝒲 is the (given) initial state and X̂(t), the free process, is a Brownian motion" (p.13) → Ŵ(0) independent of X̂ (IsDiffSol); reason: the diffusion limit is driven by a Brownian motion independent of its initial state; the proof of Theorem 14 (p.25) uses this to identify the limit as the diffusion started from π̃₁
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: "stationary distribution" of Ξ̂^k and of Ŵ (pp.18, 24) → IsStationary: a realization from π exists and every realization from π has Ξ^k(t) ∼ π for t ≥ 0; IsDiffStationary: carried by 𝒲, a diffusion from μ exists, and every one has Ŵ(t) ∼ μ; reason: the standard definition; the existence conjuncts prevent vacuous stationarity
--   - encoding: (71) with sup_{0≤s≤t}|Ŵ^k(s)| and sup_{0≤s≤t}|X̂^k(s)|, "any sample-path" → for every k ≥ 1, every path satisfying the dynamics whose counts (4) are finite (all nonnegative primitive sequences with unbounded partial sums, all initial states), every t ≥ 0 and every bound M of |X̂^k| on [0, t]: |Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + M) on [0, t]; reason: equivalent to the supremum form, also when a supremum is infinite; "any sample-path" read literally; a primitive sequence with bounded partial sums makes the maxima in (4) infinite and is not a sample path of the model
--   - encoding: expectations E|·|^q → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(|·|^q) in [0, ∞]; reason: the same value, with no junk value for non-integrable variables
--   - reading: "the stationary distributions" π̂^k_1 (Theorem 7(b), for large k) and π̂₁ (Theorem 4) → the conclusion also asserts ∃ k₀ with stationary distributions for every k ≥ k₀, and existence and uniqueness of π̂₁; (79)–(80) are asserted for every choice of stationary π^k, k ≥ k₀; reason: the theorem speaks of "the" stationary distributions, whose existence (and uniqueness) the paper takes from Theorems 7(b) and 4 and uses in the proof (p.25); quantifying over every choice is at least as strong
--   - encoding: (80) E_{π̂^k_1}|Ŵ^k(0)|^m → E_{π̂₁}|Ŵ(0)|^m → lower Lebesgue integrals in [0, ∞], with the limit asserted finite; reason: the same values; finiteness of the limit moment is part of the paper’s claim (the expectations are numbers)
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Theorem 14, p.24 (PDF 24)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Theorem 14** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 24): under the usual traffic condition `Aθ < 0` (66) and the
bounded workload condition (71), for all sufficiently large `k` network `k` has a stationary
distribution; the diffusion limit `Ŵ` has a unique stationary distribution `π̂₁`; for every choice of
stationary distributions `π^k` the workload marginals `π̂^k_1` of their diffusion scalings converge
weakly to `π̂₁` (79); and `E_{π̂^k_1}|Ŵ^k(0)|^m → E_{π̂₁}|Ŵ(0)|^m < ∞` for every real `m ∈ [0, p − 1)`
(80).

**Formalization Note.** Existence of `π^k` (`k ≥ k₀`) and existence and uniqueness of `π̂₁` are
stated: the paper takes them from Theorems 7(b) and 4. The convergence is asserted for every sequence
of stationary distributions. `|·|` is the `ℓ¹` norm; moments are lower Lebesgue integrals in
`[0, ∞]`, and the limit moment is asserted finite. The network sequence satisfies the standing
assumptions and heavy traffic (11); `H` is any matrix satisfying (17). -/
theorem theorem_14 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hAθ : S.UsualTraffic) (hBW : S.BoundedWorkload) :
    ∃ k0 : ℕ, (∀ k, k0 ≤ k → ∃ π : Measure (State R), S.IsStationary k π) ∧
      ∃ μ : ProbabilityMeasure (Fin R → ℝ), S.IsDiffStationary H μ ∧
        (∀ μ' : Measure (Fin R → ℝ), S.IsDiffStationary H μ' → μ' = μ) ∧
        ∀ π : ℕ → ProbabilityMeasure (State R), (∀ k, k0 ≤ k → S.IsStationary k (π k)) →
          Tendsto (fun k => NetSeq.wLaw k (π k)) atTop (𝓝 μ) ∧
          ∀ m : ℝ, 0 ≤ m → m < S.p - 1 →
            ∫⁻ w, ENNReal.ofReal (l1 w ^ m) ∂(μ : Measure (Fin R → ℝ)) < ⊤ ∧
            Tendsto (fun k => ∫⁻ w, ENNReal.ofReal (l1 w ^ m) ∂(NetSeq.wLaw k (π k) : Measure (Fin R → ℝ)))
              atTop (𝓝 (∫⁻ w, ENNReal.ofReal (l1 w ^ m) ∂(μ : Measure (Fin R → ℝ)))) := by sorry

end FairDiffusionLimit
