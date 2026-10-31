-- Prove2me | Theorems.Thm_FairDiffusionLimit_theorem_4
-- name    : FairDiffusionLimit.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:06.373994+00:00
-- url     : https://prove2.me/theorems/008bea9f-2bb5-433c-a108-bce4f93312e1
-- title:
--   Theorem 4 — a stable deterministic DCP makes the diffusion limit positive recurrent with a unique stationary distribution
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   Suppose the deterministic DCP (38)–(43) is stable. Then the diffusion limit $\hat W$ of Theorem 1 (the solution of the DCP (27)–(32) driven by a Brownian motion $\hat X$ with drift $\theta$ and covariance $\Upsilon$, independent of $\hat W(0)\in\mathcal W$) is
--
--   1. positive recurrent: from every initial state $x\in\mathcal W$, the expected hitting time of every open set that meets $\mathcal W$ is finite; and
--   2. has a stationary distribution $\hat\pi_1$ (a law on $\mathcal W$ such that $\hat W(0)\sim\hat\pi_1$ implies $\hat W(t)\sim\hat\pi_1$ for all $t\ge0$), and no other.
--
--   This is the existence and uniqueness of the steady state that the interchange of limits (Theorem 14) approximates.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network).
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
--   - encoding: X̂ a Brownian motion with drift θ and covariance Υ (p.13) → published Reiman84.QueueLength.IsDriftedBM θ Υ: X̂(0) = 0, every path continuous, independent Gaussian increments; reason: X̂(0) = 0 is forced by (24); continuity of every path instead of almost every path changes no law
--   - reading: "where Ŵ(0) ∈ 𝒲 is the (given) initial state and X̂(t), the free process, is a Brownian motion" (p.13) → Ŵ(0) independent of X̂ (IsDiffSol); reason: the diffusion limit is driven by a Brownian motion independent of its initial state; the proof of Theorem 14 (p.25) uses this to identify the limit as the diffusion started from π̃₁
--   - encoding: "stationary distribution" of Ξ̂^k and of Ŵ (pp.18, 24) → IsStationary: a realization from π exists and every realization from π has Ξ^k(t) ∼ π for t ≥ 0; IsDiffStationary: carried by 𝒲, a diffusion from μ exists, and every one has Ŵ(t) ∼ μ; reason: the standard definition; the existence conjuncts prevent vacuous stationarity
--   - reading: "positive recurrent" for Ŵ (Theorem 4) → PosRecurrentDiff: from every x ∈ 𝒲, the expected hitting time of every open set meeting 𝒲 is finite; reason: the paper does not define the term; the proof applies Dupuis–Williams [17], Theorem 2.6, whose notion this is
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Theorem 4, p.16 (PDF 16)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Theorem 4** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 16): if the deterministic DCP (38)–(43) is stable, then the
diffusion limit `Ŵ` of Theorem 1 is positive recurrent and has a unique stationary distribution.

**Formalization Note.** Positive recurrence is the Dupuis–Williams notion of the cited proof
(finite expected hitting time of every open set meeting `𝒲`, from every initial state in `𝒲`). -/
theorem theorem_4 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hDS : S.DetStable H) :
    S.PosRecurrentDiff H ∧ ∃ μ : Measure (Fin R → ℝ), S.IsDiffStationary H μ ∧
      ∀ μ' : Measure (Fin R → ℝ), S.IsDiffStationary H μ' → μ' = μ := by sorry

end FairDiffusionLimit
