-- Prove2me | Theorems.Thm_FairDiffusionLimit_lemma_9
-- name    : FairDiffusionLimit.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:30.330416+00:00
-- url     : https://prove2.me/theorems/d5b4476d-1e7c-4721-91e1-dd26bdac841a
-- title:
--   Lemma 9 — bounded $p$-th moments and uniform integrability under the bounded workload condition
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17). Assume the bounded workload condition (71).
--
--   1. **(Bounded $p$-th moment)** There is a constant $\kappa$ such that for every $k\ge1$, every $M>0$, every network $k$ started with $|\hat\Xi^k(0)|\le M$ and every $t\ge0$,
--   $$E\sup_{0\le s\le t}|\hat W^k(s)|^p\le\kappa(M^p+1+t^p),\tag{72}$$
--   and, for every $0\le q\le p$, $E\sup_{0\le s\le t}|\hat W^k(s)|^q\le\kappa(M^q+1+t^q)$ (73).
--   2. **(Uniform integrability in $i$)** For every sufficiently large $k$: for $m_i\to\infty$, initial states $x^i$ with $|x^i|\le m_i$ and every $t\ge0$, the family $\{|\hat W^k(m_it;x^i)/m_i|^p\}_i$ is uniformly integrable.
--   3. **(Uniform integrability in $k$)** For $m_k\to\infty$ and networks started with $|\hat\Xi^k(0)|\le m_k$, and every $t\ge0$, the family $\{|\hat W^k(m_kt)/m_k|^p\}_{k\ge1}$ is uniformly integrable.
--
--   These estimates turn the pathwise convergence of Lemma 10(a),(b) into convergence of $p$-th moments.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). Uniform integrability means $\lim_{K\to\infty}\sup_iE[Y_i;Y_i>K]=0$, each $Y_i$ on its own probability space. One constant $\kappa$ serves (72) and (73) (the page redefines $\kappa$; taking the larger one is equivalent). In (c) the claim is for every $t\ge0$.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: (71) with sup_{0≤s≤t}|Ŵ^k(s)| and sup_{0≤s≤t}|X̂^k(s)|, "any sample-path" → for every k ≥ 1, every path satisfying the dynamics whose counts (4) are finite (all nonnegative primitive sequences with unbounded partial sums, all initial states), every t ≥ 0 and every bound M of |X̂^k| on [0, t]: |Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + M) on [0, t]; reason: equivalent to the supremum form, also when a supremum is infinite; "any sample-path" read literally; a primitive sequence with bounded partial sums makes the maxima in (4) infinite and is not a sample path of the model
--   - encoding: expectations E|·|^q → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(|·|^q) in [0, ∞]; reason: the same value, with no junk value for non-integrable variables
--   - reading: (a) "Consider the sequence Ξ̂^k(t), with |Ξ̂^k(0)| ≤ M for some M > 0 … for some constant κ" → ∃ κ, ∀ k ≥ 1, ∀ M > 0, ∀ realization with |Ξ̂^k(0)| ≤ M a.s., ∀ t ≥ 0; reason: the M^p and t^p in (72) show κ is uniform in k, M, t; the stronger (uniform) reading
--   - reading: (b) "for a fixed, sufficiently large k"; (c) "Then {…} is uniformly integrable" → (b) ∃ k₀ ∀ k ≥ k₀ uniformly over the sequences and every t ≥ 0; (c) for every t ≥ 0, family over k ≥ 1; reason: "for any given t ≥ 0" of (b) also governs (c); a uniform k₀ is the stronger reading
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Lemma 9, p.22 (PDF 22)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Lemma 9** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 22), under the bounded workload condition (71):

(a) (bounded `p`-th moment) there is `κ` such that, for every `k ≥ 1`, `M > 0` and every network
`k` with `|Ξ̂^k(0)| ≤ M`, `E sup_{0≤s≤t} |Ŵ^k(s)|^p ≤ κ(M^p + 1 + t^p)` (72) and
`E sup_{0≤s≤t} |Ŵ^k(s)|^q ≤ κ(M^q + 1 + t^q)` for every `0 ≤ q ≤ p` (73);

(b) (uniform integrability) for all sufficiently large `k`, every `m_i → ∞`, initial states `x^i` with
`|x^i| ≤ m_i` and every `t ≥ 0`, the family `|Ŵ^k(m_it; x^i)/m_i|^p` is uniformly integrable in `i`;

(c) (uniform integrability) for every `m_k → ∞` and networks with `|Ξ̂^k(0)| ≤ m_k`, and every
`t ≥ 0`, the family `|Ŵ^k(m_kt)/m_k|^p` is uniformly integrable in `k`.

**Formalization Note.** `Ξ̂^k(0) = Ξ^k(0)/k`; the bound on it holds almost surely. `Ŵ^k(·; x)` is the
process of a realization from `δ_{kx}`. The suprema are taken in `[0, ∞]` and expectations are lower
Lebesgue integrals. Uniform integrability is `UnifIntegrableOn` (each variable on its own space). -/
theorem lemma_9 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hBW : S.BoundedWorkload) :
    (∃ κ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ M : ℝ, 0 < M → ∀ (μ : Measure (State R)) (Rz : NetSeq.Realization S k μ),
      (∀ᵐ ω ∂(Rz.C.P), stNorm ((k : ℝ)⁻¹ • Rz.X0 ω) ≤ M) → ∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal (l1 (S.hatW k (Rz.pd ω) s) ^ S.p)) ∂(Rz.C.P)
            ≤ ENNReal.ofReal (κ * (M ^ S.p + 1 + t ^ S.p)) ∧
        ∀ q : ℝ, 0 ≤ q → q ≤ S.p →
          ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal (l1 (S.hatW k (Rz.pd ω) s) ^ q)) ∂(Rz.C.P)
            ≤ ENNReal.ofReal (κ * (M ^ q + 1 + t ^ q))) ∧
    (∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ (m : ℕ → ℝ), Tendsto m atTop atTop → ∀ x : ℕ → State R,
      (∀ i, stNorm (x i) ≤ m i) → ∀ t : ℝ, 0 ≤ t →
      ∀ Rz : ∀ i, NetSeq.Realization S k (Measure.dirac ((k : ℝ) • x i)),
        UnifIntegrableOn Set.univ (fun i => (Rz i).C.Ω) (fun i => (Rz i).C.P)
          (fun i ω => ENNReal.ofReal (l1 ((m i)⁻¹ • S.hatW k ((Rz i).pd ω) (m i * t)) ^ S.p))) ∧
    (∀ (m : ℕ → ℝ), Tendsto m atTop atTop → ∀ (μ : ℕ → Measure (State R))
      (Rz : ∀ k, NetSeq.Realization S k (μ k)),
      (∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂((Rz k).C.P), stNorm ((k : ℝ)⁻¹ • (Rz k).X0 ω) ≤ m k) →
      ∀ t : ℝ, 0 ≤ t →
        UnifIntegrableOn {k | 1 ≤ k} (fun k => (Rz k).C.Ω) (fun k => (Rz k).C.P)
          (fun k ω => ENNReal.ofReal (l1 ((m k)⁻¹ • S.hatW k ((Rz k).pd ω) (m k * t)) ^ S.p)))
    := by sorry

end FairDiffusionLimit
