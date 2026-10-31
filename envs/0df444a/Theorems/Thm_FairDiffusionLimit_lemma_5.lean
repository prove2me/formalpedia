-- Prove2me | Theorems.Thm_FairDiffusionLimit_lemma_5
-- name    : FairDiffusionLimit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:17.092576+00:00
-- url     : https://prove2.me/theorems/4421621b-2d80-478b-a8c4-7f7e700094a1
-- title:
--   Lemma 5 — fluid limits of the $k$-th network solve the fluid model (55)–(58) (corrected: $\rho^k_r$ in (59))
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   Fix a network $k\ge1$. Let $m_i\to\infty$ and let $x^i\in\mathcal X$ be initial states of $\hat\Xi^k$ with $|x^i|\le m_i$; the processes $\hat\Xi^k(\cdot;x^i)$ are built on one probability space from the common primitives. Then every subsequence of $i$ has a further subsequence $\mathcal I$ such that, almost surely, as $i\to\infty$ along $\mathcal I$,
--   $$\frac1{m_i}\hat\Xi^k(0;x^i)\to\big(\hat w^k(0),\bar u^k(1),\bar v^k(1)\big),$$
--   $$\frac1{m_i}\Big(\hat W^k(m_it),\tilde D^k(m_it),\hat Y^k(m_it),\hat Z^k(m_it)\Big)\to\big(\hat w^k(t),\bar d^k(t),\hat y^k(t),\hat z^k(t)\big)\quad\text{u.o.c. in } t\ge0,$$
--   where the (possibly random) limit is Lipschitz continuous, solves the fluid model (55)–(59) of network $k$, and satisfies $|\hat w^k(0)|+|\bar u^k(1)|+|\bar v^k(1)|\le1$.
--
--   This is the fluid limit theorem that links the stochastic network $k$ to its fluid model, used for positive recurrence (Theorem 7(b)) and the moment stability of Lemma 10.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). The subsequence $\mathcal I$ is deterministic.
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
--   - correction: fluid model (55)–(59) with Λ̄_r(n) = ρ_r for n_r = 0 and the convention ŵ^k_r ≡ ν_r n̂^k_r (p.17) → IsFluidSol with the k-th network’s ρ^k_r in (59), n̂^k_r = ŵ^k_r/ν^k_r, and ŵ^k ≥ 0; reason: as printed Lemma 5 is false: L = R = 1, A = c = β = ν^k = 1, λ^k = 1 − 1/k (so ρ^k < ρ = 1, all standing assumptions hold), x^i with zero workload: network k is stable, the fluid limit is ŵ^k ≡ 0 with d̄^k(t) = ρ^k t, but (59) with ρ_r forces d̄^k(t) = t and then (55) gives ŵ^k(t) = k(ρ^k − 1)t < 0; with ρ^k_r (the index k appended, p.12) the limit solves the model
--   - encoding: "for any subsequence of k, there exists a further subsequence 𝒦" → φ strictly increasing, ∃ ψ strictly increasing, 𝒦 = φ ∘ ψ; reason: the same subsequences
--   - reading: "there exists a further subsequence I such that the following (a.s.) convergence holds" → a deterministic subsequence ψ, then almost surely; the limit may depend on ω; reason: the literal order of the quantifiers (the stronger reading)
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Lemma 5, p.17 (PDF 17)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Lemma 5** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 17): fix a network `k ≥ 1`. Let `m_i → ∞` and let `x^i` be initial
states of `Ξ̂^k` with `|x^i| ≤ m_i`. For the coupled processes `Ξ̂^k(·; x^i)` and every subsequence
there is a further subsequence `ℐ` along which, almost surely,
`Ξ̂^k(0; x^i)/m_i → (ŵ^k(0), ū^k(1), v̄^k(1))` and
`(Ŵ^k(m_it), D̃^k(m_it), Ŷ^k(m_it), Ẑ^k(m_it))/m_i → (ŵ^k(t), d̄^k(t), ŷ^k(t), ẑ^k(t))` u.o.c. in
`t ≥ 0`, where the limit is Lipschitz continuous, solves the fluid model (55)–(58), and
`|ŵ^k(0)| + |ū^k(1)| + |v̄^k(1)| ≤ 1`.

**Formalization Note.** The processes `Ξ̂^k(·; x^i)` live on one primitive space `C` (the paper's
coupled copies, p. 10): network `k` is started from the unscaled state `k x^i`, so `Ξ̂^k(0) = x^i`. The
subsequence `ℐ = φ ∘ ψ` is deterministic; the limit may depend on `ω`. The fluid model uses `ρ^k_r` in
(59) (see `IsFluidSol`). -/
theorem lemma_5 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (k : ℕ) (hk : 1 ≤ k) (m : ℕ → ℝ) (hm : Tendsto m atTop atTop) (x : ℕ → State R)
    (hx : ∀ i, stNorm (x i) ≤ m i) (C : NetSeq.PrimSpace S) (N : ℕ → ℝ → C.Ω → Fin R → ℕ)
    (hN : ∀ i, S.IsPathOn C k (fun _ => (k : ℝ) • x i) (N i))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᵐ ω ∂(C.P),
      ∃ (ub vb : Fin R → ℝ) (w d : ℝ → Fin R → ℝ) (y : ℝ → Fin L → ℝ) (z : ℝ → Fin (R - L) → ℝ),
        S.IsFluidSol H k ub vb w d y z ∧
        (∃ K : NNReal, LipschitzOnWith K w (Set.Ici 0) ∧ LipschitzOnWith K d (Set.Ici 0) ∧
          LipschitzOnWith K y (Set.Ici 0) ∧ LipschitzOnWith K z (Set.Ici 0)) ∧
        l1 (w 0) + l1 ub + l1 vb ≤ 1 ∧
        Tendsto (fun n => (m (φ (ψ n)))⁻¹ •
            S.hatXi k (C.pd (fun _ => (k : ℝ) • x (φ (ψ n))) (N (φ (ψ n))) ω) 0)
          atTop (𝓝 (w 0, ub, vb)) ∧
        Reiman84.QueueLength.UocTendsto (fun n t => (m (φ (ψ n)))⁻¹ •
          S.hatW k (C.pd (fun _ => (k : ℝ) • x (φ (ψ n))) (N (φ (ψ n))) ω) (m (φ (ψ n)) * t)) w ∧
        Reiman84.QueueLength.UocTendsto (fun n t => (m (φ (ψ n)))⁻¹ •
          S.tildeD k (C.pd (fun _ => (k : ℝ) • x (φ (ψ n))) (N (φ (ψ n))) ω) (m (φ (ψ n)) * t)) d ∧
        Reiman84.QueueLength.UocTendsto (fun n t => (m (φ (ψ n)))⁻¹ •
          S.hatY k (C.pd (fun _ => (k : ℝ) • x (φ (ψ n))) (N (φ (ψ n))) ω) (m (φ (ψ n)) * t)) y ∧
        Reiman84.QueueLength.UocTendsto (fun n t => (m (φ (ψ n)))⁻¹ •
          S.hatZ H k (C.pd (fun _ => (k : ℝ) • x (φ (ψ n))) (N (φ (ψ n))) ω) (m (φ (ψ n)) * t))
          z := by sorry

end FairDiffusionLimit
