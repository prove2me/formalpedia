-- Prove2me | Theorems.Thm_FairDiffusionLimit_theorem_7_b
-- name    : FairDiffusionLimit.theorem_7_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:19.539532+00:00
-- url     : https://prove2.me/theorems/cced276a-c48e-424e-8f58-ad6bd79454b5
-- title:
--   Theorem 7(b) — for large $k$ the network is positive Harris recurrent with a unique stationary law and a finite $(p-1)$-th workload moment
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   Suppose the deterministic DCP (38)–(43) is stable. Then for all sufficiently large $k$:
--
--   1. $\hat\Xi^k$ is positive (Harris) recurrent;
--   2. it has a unique stationary distribution $\hat\pi^k$;
--   3. the stationary workload has a finite $(p-1)$-th moment:
--   $$E_{\hat\pi^k}|\hat W^k(0)|^{p-1}<\infty. \tag{61}$$
--
--   These are the stationary distributions whose limit Theorem 14 identifies.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). Stationarity is stated for the unscaled $\Xi^k$; $\hat\pi^k$ is its image under $x\mapsto x/k$.
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
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: "stationary distribution" of Ξ̂^k and of Ŵ (pp.18, 24) → IsStationary: a realization from π exists and every realization from π has Ξ^k(t) ∼ π for t ≥ 0; IsDiffStationary: carried by 𝒲, a diffusion from μ exists, and every one has Ŵ(t) ∼ μ; reason: the standard definition; the existence conjuncts prevent vacuous stationarity
--   - reading: "positive recurrent" for Ξ̂^k (Theorem 7(b)); p.16: "the positive (Harris) recurrence of the pre-limit networks" → PositiveHarris: a nonzero σ-finite φ such that from every initial state every set of positive φ-measure is visited for infinite total time a.s., and a stationary distribution exists; reason: the paper does not define the term; p.16 and the cited Dai–Meyn [14] use positive Harris recurrence
--   - encoding: expectations E|·|^q → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(|·|^q) in [0, ∞]; reason: the same value, with no junk value for non-integrable variables
--   - encoding: Ξ̂^k positive recurrent with unique stationary distribution π̂^k → stated for the unscaled Ξ^k, with π̂^k the image of its stationary law under x ↦ x/k; reason: Ξ̂^k(t) = Ξ^k(k²t)/k: recurrence and stationarity are unchanged by the time and space scaling
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Theorem 7(b), p.18 (PDF 18)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Theorem 7(b)** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 18): if the deterministic DCP (38)–(43) is stable, then for all
sufficiently large `k`, `Ξ̂^k` is positive (Harris) recurrent and has a unique stationary distribution
`π̂^k`, and the stationary workload has a finite `(p − 1)`-th moment, `E_{π̂^k}|Ŵ^k(0)|^{p−1} < ∞` (61).

**Formalization Note.** Stationarity is stated for the unscaled `Ξ^k`; `π̂^k` is the image of its
stationary law under `x ↦ x/k`, so `Ŵ^k(0) = W^k(0)/k`. Positive recurrence is positive Harris
recurrence (`PositiveHarris`). -/
theorem theorem_7_b {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hDS : S.DetStable H) :
    ∀ᶠ k in atTop, S.PositiveHarris k ∧ ∃ π : Measure (State R), S.IsStationary k π ∧
      (∀ π' : Measure (State R), S.IsStationary k π' → π' = π) ∧
      ∫⁻ x, ENNReal.ofReal (l1 ((k : ℝ)⁻¹ • x.1) ^ (S.p - 1)) ∂π < ⊤ := by sorry

end FairDiffusionLimit
