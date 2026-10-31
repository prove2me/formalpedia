-- Prove2me | Theorems.Thm_FairDiffusionLimit_lemma_10
-- name    : FairDiffusionLimit.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:26.089957+00:00
-- url     : https://prove2.me/theorems/27eaf176-2ac6-4e52-b6b6-d245c7d5d883
-- title:
--   Lemma 10 — almost-sure and $L^p$ fluid-scale decay of the workload after a fixed time $t_0$
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17). Assume the usual traffic condition $A\theta<0$ (66). There is a time $t_0$ such that:
--
--   1. **(a)** for all sufficiently large $k$, all $m_i\to\infty$ and initial states $x^i$ with $|x^i|\le m_i$ (coupled processes), almost surely $\frac1{m_i}\hat W^k(m_it;x^i)\to0$ uniformly on compact subsets of $t\ge t_0$ as $i\to\infty$;
--   2. **(b)** for all $m_k\to\infty$ and initial states with $|\hat\Xi^k(0)|\le m_k$ (coupled across $k$ through the common primitives), almost surely $\frac1{m_k}\hat W^k(m_kt)\to0$ uniformly on compact subsets of $t\ge t_0$ as $k\to\infty$;
--
--   and if moreover the bounded workload condition (71) holds,
--
--   3. **(c)** for all sufficiently large $k$ and $m_i,x^i$ as in (a), and every $t\ge t_0$, $\displaystyle\lim_{i\to\infty}E\frac1{m_i^p}|\hat W^k(m_it;x^i)|^p=0$;
--   4. **(d)** for $m_k$ and initial states as in (b), and every $t\ge t_0$, $\displaystyle\lim_{k\to\infty}E\frac1{m_k^p}|\hat W^k(m_kt)|^p=0$.
--
--   These are the pathwise and moment forms of uniform stability used for Proposition 11.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). In (b) the initial states are random, independent of the primitives. "Sufficiently large $k$" is a threshold $k_0$ uniform over the sequences.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - reading: "many copies of the same network, each starting from a different initial state … Ξ(t; x)" (p.10); almost-sure claims across x and k → all processes on one PrimSpace (the common base primitives (12)); network k from x is started at the unscaled state k·x, so Ξ̂^k(0) = x; reason: the almost-sure statements across different initial states and k need a common probability space; (12) provides it
--   - encoding: (71) with sup_{0≤s≤t}|Ŵ^k(s)| and sup_{0≤s≤t}|X̂^k(s)|, "any sample-path" → for every k ≥ 1, every path satisfying the dynamics whose counts (4) are finite (all nonnegative primitive sequences with unbounded partial sums, all initial states), every t ≥ 0 and every bound M of |X̂^k| on [0, t]: |Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + M) on [0, t]; reason: equivalent to the supremum form, also when a supremum is infinite; "any sample-path" read literally; a primitive sequence with bounded partial sums makes the maxima in (4) infinite and is not a sample path of the model
--   - encoding: expectations E|·|^q → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(|·|^q) in [0, ∞]; reason: the same value, with no junk value for non-integrable variables
--   - reading: (c), (d) without a stated range of t; "for any sufficiently large k" after the sequences → (c), (d) for every t ≥ t₀; ∃ k₀ before the sequences; reason: the claims are false in general for t < t₀ and parallel (a), (b); a uniform k₀ is the stronger reading (it comes from Theorem 7(a))
--   - reading: (b) "the sequence of initial states {Ξ̂^k(0)}" with "with probability one" → random initial states X0 k on the common primitive space, independent of the primitives, with |Ξ̂^k(0)| ≤ m_k a.s.; reason: almost-sure convergence across k needs a common space; (12) couples the networks
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Lemma 10, p.22 (PDF 22)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Lemma 10** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 22): under the usual traffic condition (66) there is a time `t₀` such
that

(a) for all sufficiently large `k`, every `m_i → ∞` and initial states `x^i` with `|x^i| ≤ m_i`,
almost surely `Ŵ^k(m_it; x^i)/m_i → 0` u.o.c. in `t ≥ t₀` as `i → ∞`;

(b) for every `m_k → ∞` and initial states with `|Ξ̂^k(0)| ≤ m_k`, almost surely
`Ŵ^k(m_kt)/m_k → 0` u.o.c. in `t ≥ t₀` as `k → ∞`;

and, if moreover the bounded workload condition (71) holds,

(c) for all sufficiently large `k` and `m_i`, `x^i` as in (a), `lim_i E|Ŵ^k(m_it; x^i)|^p/m_i^p = 0`;

(d) for `m_k` and initial states as in (b), `lim_k E|Ŵ^k(m_kt)|^p/m_k^p = 0`.

**Formalization Note.** (a) and (b) are on one primitive space (the coupled processes, p. 10): in (a)
network `k` is started from `k x^i`; in (b) network `k` from a random initial state `X0 k`
independent of the primitives. "u.o.c. in `t ≥ t₀`" is uniform convergence on every `[t₀, T]`. In
(c), (d) the claims are for every `t ≥ t₀`, and the expectations are over any realization. "For
sufficiently large `k`" is uniform over the sequences. -/
theorem lemma_10 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hAθ : S.UsualTraffic) :
    ∃ t0 : ℝ,
      (∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ (m : ℕ → ℝ), Tendsto m atTop atTop → ∀ x : ℕ → State R,
        (∀ i, stNorm (x i) ≤ m i) → ∀ (C : NetSeq.PrimSpace S) (N : ℕ → ℝ → C.Ω → Fin R → ℕ),
        (∀ i, S.IsPathOn C k (fun _ => (k : ℝ) • x i) (N i)) →
        ∀ᵐ ω ∂(C.P), ∀ T ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ t ∈ Set.Icc t0 T,
          l1 ((m i)⁻¹ • S.hatW k (C.pd (fun _ => (k : ℝ) • x i) (N i) ω) (m i * t)) < ε) ∧
      (∀ (m : ℕ → ℝ), Tendsto m atTop atTop → ∀ (C : NetSeq.PrimSpace S) (X0 : ℕ → C.Ω → State R)
        (N : ℕ → ℝ → C.Ω → Fin R → ℕ), (∀ k : ℕ, 1 ≤ k → S.IsPathOn C k (X0 k) (N k)) →
        (∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂(C.P), stNorm ((k : ℝ)⁻¹ • X0 k ω) ≤ m k) →
        ∀ᵐ ω ∂(C.P), ∀ T ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t ∈ Set.Icc t0 T,
          l1 ((m k)⁻¹ • S.hatW k (C.pd (X0 k) (N k) ω) (m k * t)) < ε) ∧
      (S.BoundedWorkload →
        (∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ (m : ℕ → ℝ), Tendsto m atTop atTop → ∀ x : ℕ → State R,
          (∀ i, stNorm (x i) ≤ m i) → ∀ t : ℝ, t0 ≤ t →
          ∀ Rz : ∀ i, NetSeq.Realization S k (Measure.dirac ((k : ℝ) • x i)),
            Tendsto (fun i => ∫⁻ ω, ENNReal.ofReal
                (l1 ((m i)⁻¹ • S.hatW k ((Rz i).pd ω) (m i * t)) ^ S.p) ∂((Rz i).C.P))
              atTop (𝓝 0)) ∧
        (∀ (m : ℕ → ℝ), Tendsto m atTop atTop → ∀ (μ : ℕ → Measure (State R))
          (Rz : ∀ k, NetSeq.Realization S k (μ k)),
          (∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂((Rz k).C.P), stNorm ((k : ℝ)⁻¹ • (Rz k).X0 ω) ≤ m k) →
          ∀ t : ℝ, t0 ≤ t →
            Tendsto (fun k => ∫⁻ ω, ENNReal.ofReal
                (l1 ((m k)⁻¹ • S.hatW k ((Rz k).pd ω) (m k * t)) ^ S.p) ∂((Rz k).C.P))
              atTop (𝓝 0))) := by sorry

end FairDiffusionLimit
