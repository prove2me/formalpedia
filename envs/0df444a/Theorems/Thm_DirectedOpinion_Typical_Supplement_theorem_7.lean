-- Prove2me | Theorems.Thm_DirectedOpinion_Typical_Supplement_theorem_7
-- name    : DirectedOpinion.Typical.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:33:15.950852+00:00
-- url     : https://prove2.me/theorems/3da9753a-c420-4486-a295-5892492179a5
-- title:
--   Theorem 7, p. 24 (corrected: Lipschitz signal and initial-opinion kernels) — two uniform vertices: limit sequences for R^(t) and B^(t), and 𝓑^(t) converges a.s.
-- statement:
--   Let $\{G(V_n,E_n;\mathscr A_n):n\ge1\}$ be a sequence of random vertex-weighted directed graphs with parameters $c\in[0,1)$, $d\in(0,1]$, $c+d\le1$, carrying the opinion process
--   $$R_i^{(t+1)}=\sum_{r=1}^{D_i^-}C(i,r)R^{(t)}_{L(i,r)}+W_i^{(t)}+(1-c-d)R_i^{(t)},\qquad\text{i.e. } \mathbf R^{(t+1)}=\bar\Delta\mathbf R^{(t)}+\mathbf W^{(t)},$$
--   and let $\mathbf B^{(t)}=\sum_{r=0}^{t}\bar\Delta^r\mathbf W^{(r)}$ be the time-reversed sums. Here the signals $W_i^{(t)}$ are, given the graph, independent across vertices and i.i.d. in time with law $\nu(\mathbf X_i)$ depending on the mark $\mathbf X_i$ of the vertex, and the initial opinions are $R_i^{(0)}=\varphi(\mathbf X_i,V_i)$ with independent uniforms $V_i$. Write $\mathscr F_n=\sigma(\mathscr A_n)$ and $\mathbb E_n[\,\cdot\,]=E[\,\cdot\mid\mathscr F_n]$.
--
--   Assume that
--   1. the sequence admits a strong coupling (Definition 4, as printed) with a marked, rooted, directed graph $\mathcal G(\boldsymbol{\mathcal X})$;
--   2. $d>0$ (the condition of Theorem 1);
--   3. $d_1(\nu(x),\nu(\tilde x))\le K\rho(x,\tilde x)$ for all marks $x,\tilde x$, and the law of $\varphi(x,V)$ satisfies the same bound with the same constant $K$.
--
--   Let $g,h:[-1,1]\to\mathbb R$ be continuous, and let $I_n,J_n$ be independent and uniformly distributed on $V_n$. Then for every $k\ge1$ there exist, on an extension of the probability space, random sequences $\{(\mathcal R^{(t)},\mathcal B^{(t)}):t\ge0\}$ and $\{(\hat{\mathcal R}^{(t)},\hat{\mathcal B}^{(t)}):t\ge0\}$ with values in $[-1,1]^2$, i.i.d. with a law that is the same for every $n$ and independent of $\mathscr F_n$, such that, as $n\to\infty$,
--   $$\sup_{0\le t\le k}\mathbb E_n\Bigl[\bigl|(g(R^{(t)}_{I_n})-g(\mathcal R^{(t)}))(h(R^{(t)}_{J_n})-h(\hat{\mathcal R}^{(t)}))\bigr|\Bigr]\xrightarrow{P}0,\qquad \sup_{0\le t\le k}\mathbb E_n\Bigl[\bigl|(g(B^{(t)}_{I_n})-g(\mathcal B^{(t)}))(h(B^{(t)}_{J_n})-h(\hat{\mathcal B}^{(t)}))\bigr|\Bigr]\xrightarrow{P}0 .$$
--   Moreover, $\mathcal B^{(t)}$ and $\hat{\mathcal B}^{(t)}$ converge almost surely as $t\to\infty$.
--
--   The theorem states the two-copy error estimates used in the paper’s second-moment argument for Theorem 2 (pp. 24, 27).
--
--   **Formalization Note** The model is the published `GraphSeqModel` of the base mission: the $m$-th graph has the $m+1$ vertices $\{0,\dots,m\}$; signals are $W_i^{(t)}=\zeta(\mathbf X_i,U_i^{(t)})$ with independent uniforms (the quantile representation of $\nu$). The limit sequences live on a probability space $\Omega'$ with a measure-preserving map $\pi:\Omega'\to\Omega$; every graph quantity is composed with $\pi$, and $\mathbb E_n$ is the conditional expectation given $\pi^{-1}\mathscr F_n$. For each $n$ the two sequences are given; their common law $\mu$ is fixed. They are indexed by every $t\ge0$, so that the almost-sure convergence refers to the same sequences; the two suprema are finite maxima over $0\le t\le k$. Continuity on $[-1,1]$ is the paper's "bounded and continuous": all opinions and all limit variables lie in $[-1,1]$. Convergence in probability is `TendstoInMeasure`. The integrands are bounded and measurable, so no conditional expectation can be the junk value $0$.
--
--   Differences from the source:
--
--   - correction: the hypotheses are "the conditions of Theorem 1" (d > 0) → the signal kernel is also d₁-Lipschitz in the mark with constant K; reason: paper.md slip 3, the proof on p. 26 uses d₁(ν(x), ν(x̃)) ≤ Kρ(x, x̃) through the term Kρ(X_{I_n}, 𝓧_∅); without some continuity of ν the claim fails (marks a_i = (−1)^n/n, no edges, single-vertex limit graph with attribute 0, R^(0) ≡ 0, ν = δ_d for a > 0 and δ_{−d} for a < 0); only kernels that are not K-Lipschitz for any K are excluded
--   - correction: R^(0) is only conditionally independent of the signals given the graph (p. 6) → R_i^(0) = φ(X_i, V_i) with V_i i.i.d. uniform independent of everything else, and x ↦ law φ(x, V) d₁-Lipschitz with the same K; reason: paper.md slip 13; R^(0) ≡ (−1)^n with g = h = id and t = 0 is a counterexample to the R-statement; the B-statement does not involve R^(0)
--   - correction: Definition 4's isomorphism (Definition 2) forgets the order of inbound neighbours → the isomorphism sends the r-th inbound neighbour to the r-th, and the coupling events are measurable subsets of the events (4); reason: paper.md slip 4, the proof on p. 26 pairs C(∅, j) with C(I_n, j); this is the published CoupledAt of the base mission
--   - reading: there exist i.i.d. random sequences whose distribution does not depend on ℱ_n → on an extension (Ω′, P′, π) of the probability space, for each n two independent sequences with one common law μ not depending on n, jointly independent of π⁻¹ℱ_n; reason: the proof (pp. 24–25) builds them from fresh uniforms and an extended limit graph; "does not depend on ℱ_n" is read as in the base mission's Theorem 2
--   - encoding: sequences indexed by 0 ≤ t ≤ k → sequences indexed by all t ≥ 0 with values in [−1, 1]², suprema over 0 ≤ t ≤ k; reason: the a.s. convergence of 𝓑^(k) as k → ∞ needs the same family at every time; [−1, 1] makes g(𝓡^(t)) meaningful
--   - encoding: g, h : [−1, 1] → ℝ bounded and continuous → g, h : ℝ → ℝ continuous on [−1, 1]; reason: every opinion lies in [−1, 1], and continuity on the compact interval implies boundedness
--   - encoding: graphs G(V_n, E_n; 𝒜_n), n ≥ 1, and conditional convergence in probability → the m-th graph has m + 1 vertices; 𝔼_n conditions on σ(𝒜_n); →P is TendstoInMeasure; reason: n = m + 1 avoids an empty uniform-vertex type; attrs is precisely 𝒜_n and convergence in measure is convergence in probability for a probability measure
--   - generalization: the limit graph is locally finite (§7.2, p. 23), with finite in- and out-degrees → in-degrees are finite by the ordered-list encoding; no restriction is placed on out-degrees; reason: all source locally finite graphs have this encoding; the finite-time recursions and reversed sums use only finite inbound dependencies, so the statement also covers infinite out-degree. No source instance is excluded
--   - generalization: weight vectors at distinct vertices are conditionally independent given 𝒜_n (p. 6) → GraphSeqModel permits dependent weight vectors, while retaining the full marked-graph strong coupling; reason: the product-limit theorem conditions on and couples the entire marked graph; it does not use separate independence of weight vectors. Source conditionally independent weights are a special case
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 24, Theorem 7; proof pp. 24–27 (the (2 + K)ϵ bound, p. 26)

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_GraphSeq
import Definitions.Def_DirectedOpinion_Typical_Supplement_StrongCouplingAsPrinted

namespace DirectedOpinion.Typical.Supplement

open MeasureTheory ProbabilityTheory Set Filter Topology

universe u

/-- Theorem 7, p. 24. Under a strong coupling (Definition 4 as printed) with a limit graph of law
`μlim`, with `d > 0`, a signal kernel `ν(x) = law ζ(x, U)` that is `d₁`-Lipschitz in the mark with
constant `K`, and initial opinions `R_i^(0) = φ(X_i, V_i)` whose kernel is `d₁`-Lipschitz with the
same `K`: for all `g`, `h` continuous on `[−1, 1]` and every `k ≥ 1` there are an extension
`π : (Ω', P') → (Ω, P)` of the probability space and, for every `m`, two random sequences
`L m = (𝓡^(t), 𝓑^(t))_{t ≥ 0}` and `Lhat m = (𝓡̂^(t), 𝓑̂^(t))_{t ≥ 0}` on `Ω'` with values in
`[−1, 1]²`, i.i.d. with one law `μ` not depending on `m`, jointly independent of `ℱ_m = σ(𝒜_m)`,
such that, with `𝔼_m = E[· | ℱ_m]` (pulled back along `π`),
`max_{t ≤ k} 𝔼_m|(g(R_{I_m}^(t)) − g(𝓡^(t)))(h(R_{J_m}^(t)) − h(𝓡̂^(t)))| → 0` and
`max_{t ≤ k} 𝔼_m|(g(B_{I_m}^(t)) − g(𝓑^(t)))(h(B_{J_m}^(t)) − h(𝓑̂^(t)))| → 0` in probability,
and `𝓑^(t)`, `𝓑̂^(t)` converge almost surely as `t → ∞`. -/
theorem theorem_7 {Ω : Type u} {A : Type*} [MeasurableSpace Ω] [MetricSpace A]
    [MeasurableSpace A] [BorelSpace A] [PolishSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ) (c d K : ℝ)
    (μlim : Measure (LimGraph A)) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hSC : StrongCouplingAsPrinted P S 𝓖 μlim) (hK : KernelLipschitz ζ K)
    (hK0 : KernelLipschitz φ K)
    (g h : ℝ → ℝ) (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) (hh : ContinuousOn h (Icc (-1 : ℝ) 1))
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (μ : Measure (ℕ → ℝ × ℝ)) (L Lhat : ℕ → Ω' → ℕ → ℝ × ℝ),
      MeasurePreserving π P' P ∧
      -- the limit sequences take values in `[−1, 1]²`
      (∀ m ω' t, (L m ω' t).1 ∈ Icc (-1 : ℝ) 1 ∧ (L m ω' t).2 ∈ Icc (-1 : ℝ) 1) ∧
      (∀ m ω' t, (Lhat m ω' t).1 ∈ Icc (-1 : ℝ) 1 ∧ (Lhat m ω' t).2 ∈ Icc (-1 : ℝ) 1) ∧
      -- i.i.d. with a law `μ` that does not depend on `m`, and independent of `ℱ_m`
      (∀ m, HasLaw (L m) μ P') ∧ (∀ m, HasLaw (Lhat m) μ P') ∧
      (∀ m, IndepFun (L m) (Lhat m) P') ∧
      (∀ m, Indep (MeasurableSpace.comap (fun ω' => (L m ω', Lhat m ω')) inferInstance)
        (MeasurableSpace.comap (fun ω' => S.attrs m (π ω')) inferInstance) P') ∧
      -- the trajectories `R`
      TendstoInMeasure P'
        (fun m ω' => (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (fun t =>
          (P'[fun ω'' =>
              |(g (S.R ζ φ c d m t (π ω'') (S.I m (π ω''))) - g (L m ω'' t).1) *
                (h (S.R ζ φ c d m t (π ω'') (S.J m (π ω''))) - h (Lhat m ω'' t).1)|
            | MeasurableSpace.comap (fun ω'' => S.attrs m (π ω'')) inferInstance]) ω'))
        atTop (fun _ => 0) ∧
      -- the time-reversed sums `B^(t) = Σ_{r ≤ t} Δ̄^r W^(r)`
      TendstoInMeasure P'
        (fun m ω' => (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (fun t =>
          (P'[fun ω'' =>
              |(g (revPartial (S.G m (π ω'')) c d (fun r i => S.W ζ m r i (π ω'')) t
                    (S.I m (π ω''))) - g (L m ω'' t).2) *
                (h (revPartial (S.G m (π ω'')) c d (fun r i => S.W ζ m r i (π ω'')) t
                    (S.J m (π ω''))) - h (Lhat m ω'' t).2)|
            | MeasurableSpace.comap (fun ω'' => S.attrs m (π ω'')) inferInstance]) ω'))
        atTop (fun _ => 0) ∧
      -- `𝓑^(t)` and `𝓑̂^(t)` converge almost surely as `t → ∞`
      (∀ m, ∀ᵐ ω' ∂P', ∃ b : ℝ, Tendsto (fun t => (L m ω' t).2) atTop (𝓝 b)) ∧
      (∀ m, ∀ᵐ ω' ∂P', ∃ b : ℝ, Tendsto (fun t => (Lhat m ω' t).2) atTop (𝓝 b)) := by sorry

end DirectedOpinion.Typical.Supplement
