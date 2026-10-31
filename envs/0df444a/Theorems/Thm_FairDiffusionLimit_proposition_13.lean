-- Prove2me | Theorems.Thm_FairDiffusionLimit_proposition_13
-- name    : FairDiffusionLimit.proposition_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:18.809708+00:00
-- url     : https://prove2.me/theorems/28241b6d-abc8-4691-ac9a-347f2afed2bc
-- title:
--   Proposition 13 — the stationary distributions $\hat\pi^k$ are tight with uniformly bounded $(p-1)$-th moments
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17). Assume the usual traffic condition (66) and the bounded workload condition (71). There is $k_0$ such that, for every choice of stationary distributions $\pi^k$ of the networks $k\ge k_0$, with $\hat\pi^k$ the stationary distribution of $\hat\Xi^k$ (the image of $\pi^k$ under $x\mapsto x/k$):
--
--   1. $\{\hat\pi^k\}_{k\ge k_0}$ is tight on $\mathcal X$;
--   2. $\sup_{k\ge k_0}E_{\hat\pi^k}|\hat\Xi^k(0)|^{p-1}<\infty$.
--
--   Tightness gives convergent subsequences of the stationary laws; the moment bound gives the convergence of moments in Theorem 14.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network).
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: "stationary distribution" of Ξ̂^k and of Ŵ (pp.18, 24) → IsStationary: a realization from π exists and every realization from π has Ξ^k(t) ∼ π for t ≥ 0; IsDiffStationary: carried by 𝒲, a diffusion from μ exists, and every one has Ŵ(t) ∼ μ; reason: the standard definition; the existence conjuncts prevent vacuous stationarity
--   - encoding: (71) with sup_{0≤s≤t}|Ŵ^k(s)| and sup_{0≤s≤t}|X̂^k(s)|, "any sample-path" → for every k ≥ 1, every path satisfying the dynamics whose counts (4) are finite (all nonnegative primitive sequences with unbounded partial sums, all initial states), every t ≥ 0 and every bound M of |X̂^k| on [0, t]: |Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + M) on [0, t]; reason: equivalent to the supremum form, also when a supremum is infinite; "any sample-path" read literally; a primitive sequence with bounded partial sums makes the maxima in (4) infinite and is not a sample path of the model
--   - encoding: expectations E|·|^q → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(|·|^q) in [0, ∞]; reason: the same value, with no junk value for non-integrable variables
--   - reading: "the sequence of stationary distributions {π̂^k}" and sup_k → ∃ k₀; for every choice of stationary π^k, k ≥ k₀, tightness of {π̂^k}_{k≥k₀} and sup_{k≥k₀}; reason: π̂^k is defined only for large k (Theorem 7(b)); quantifying over every choice is at least as strong
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Proposition 13, p.24 (PDF 24)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Proposition 13** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 24): under (66) and (71) the stationary distributions `π̂^k` are
tight on `𝒳`, and `sup_k E_{π̂^k}|Ξ̂^k(0)|^{p−1} < ∞`.

**Formalization Note.** Stated for every choice of stationary distributions `π^k` of the networks
`k ≥ k₀` (`π̂^k` its image under `x ↦ x/k`); `π̂^k` is defined only for large `k` (Theorem 7(b)). -/
theorem proposition_13 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hAθ : S.UsualTraffic) (hBW : S.BoundedWorkload) :
    ∃ k0 : ℕ, ∀ π : ℕ → Measure (State R), (∀ k, k0 ≤ k → S.IsStationary k (π k)) →
      IsTightMeasureSet {ν | ∃ k, k0 ≤ k ∧ ν = NetSeq.hatLaw k (π k)} ∧
      ∃ Cb : ℝ, ∀ k, k0 ≤ k →
        ∫⁻ x, ENNReal.ofReal (stNorm x ^ (S.p - 1)) ∂(NetSeq.hatLaw k (π k)) ≤ ENNReal.ofReal Cb := by sorry

end FairDiffusionLimit
