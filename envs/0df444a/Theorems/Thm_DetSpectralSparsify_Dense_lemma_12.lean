-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_12
-- name    : DetSpectralSparsify.Dense.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:35.494615+00:00
-- url     : https://prove2.me/theorems/20467c7e-21a2-4632-b0b2-7aaf88da59f5
-- title:
--   Lemma 12 (Expander sparsification) — O(n₀ϕ⁻²ε⁻²L) edges; dense (32) and sparse (33) running times
-- statement:
--   Fix $c_0>0$ ($\delta=\Omega(d)$ read as $\delta_G\ge c_0d$). Let $G$ be a weighted multigraph on $n$ vertices whose non-loop edge weights lie in $[1,2]$ (loops of nonnegative weight), with $\Phi(G)\ge\phi>0$, $d\ge1$ and $\deg_G(v)\ge c_0d$ for all $v$, and let $0<\varepsilon\le1/2$ with $\varepsilon^{-1}\le n$. Put $n_0:=n+\mathrm{vol}_G(V)/d$ and $m_0:=m+\mathrm{vol}_G(V)$, let $\hat n\ge n_0$, $\hat m\ge m_0$ be ambient upper bounds, and
--   $$L:=\max\Big\{2,\ \log\frac{64(\hat n+\hat m)^4}{\varepsilon\phi}\Big\}\tag{17}$$
--   Then one can construct a $(1\pm\varepsilon)$-spectral sparsifier $H$ of $G$, a reweighted subgraph, with
--   $$|E(H)|\le C\,n_0\,\phi^{-2}\varepsilon^{-2}L \tag{31}$$
--   edges. The sparse implementation takes
--   $$C\big(m_0+n_0m_0\,\phi^{-3}\varepsilon^{-5/2}L^3\big)\tag{33}$$
--   steps, and for every achievable matrix multiplication exponent $\alpha>2$ the dense implementation takes
--   $$C\big(m_0+(n_0^{\alpha}\log n_0+n_0^2L^{\kappa}+m_0)\,\phi^{-2}\varepsilon^{-2}L\big)\tag{32}$$
--   steps, with the constants $C$, $\kappa$ independent of the instance.
--
--   The routine is called on every cluster by the one-scale algorithm (Algorithm 7).
--
--   **Formalization Note** The input is $(G,\hat n,\hat m,\varepsilon,d,\phi)$ in `graphInput G [n̂, m̂] [ε, d, ϕ]`; the output is decoded by `decodeGraph`. Constants are chosen after $c_0$ (and after $\alpha$ for the dense implementation) and before the instance.
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - reading: dense time with the factor n^ω, ω the infimum of matrix multiplication exponents (p.5) → for every α > 2 with `Achievable α` (some program multiplies n×n real matrices in C(n+1)^α steps) there is a dense program whose bound has n^α; reason: ω need not be attained; the bound is meaningful for exponents actually achieved by an algorithm, and holds for every one of them; α > 2 is the explicit reading prescribed by the BRIEF, allowing lower-degree polylogarithmic work to be absorbed in n^α
--   - reading: δ = Ω(d) → for every c₀ > 0 the hypothesis δ ≥ c₀ d, with programs and constants depending on c₀ only; reason: Ω in a hypothesis; the statement covers every value of the hidden constant
--   - reading: weighted multigraph → self-loops of nonnegative weight; reason: the clusters Q_i = F[U]⟨V_i⟩ to which the lemma is applied carry loops of weight ≥ 0
--   - reading: a (1 ± ε)-spectral sparsifier: a weighted graph H on V(G) with (1−ε)L_G ⪯ L_H ⪯ (1+ε)L_G (Definition 2) → H additionally is a reweighted subgraph of G: each edge of H has positive weight and joins two distinct vertices joined by a non-loop edge of G (`IsReweightedSubgraph`); reason: the abstract and p.1 describe the output as a reweighted subgraph; the stronger reading is the one the algorithm delivers (every recursive output is supported on its input)
--   - generalization: L by (17) using ambient upper bounds on the vertex and edge counts (of the graphs used, including the regularized graph with N = O(n₀), M = O(m₀)) → L computed from inputs n̂ ≥ n₀ and m̂ ≥ m₀; reason: N ≤ C n₀ and M ≤ C m₀ change L by at most an additive constant, absorbed since L ≥ 2; the Lean statement allows every source choice of ambient bounds and smaller ones
--   - encoding: the standing assumption ε⁻¹ ≤ n for theorems producing a spectral sparsifier (p.5) → hypothesis ε⁻¹ ≤ n; reason: the section's standing assumption made explicit
--   - encoding: bounds containing ϕ⁻¹ → hypothesis 0 < ϕ; reason: ϕ⁻² is meaningful only for ϕ > 0
--   - encoding: L^{O(1)} → L^κ with a natural κ chosen with the program; reason: spells out the O(1) exponent
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.21, Lemma 12 (with Algorithm 6); L from (17), p.13

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 12 (Expander sparsification), p.21. For every `c₀ > 0` (`δ = Ω(d)` read as `δ ≥ c₀ d`):
for a multigraph `G` with non-loop weights in `[1,2]`, `Φ(G) ≥ ϕ`, `d ≥ 1`, `δ ≥ c₀ d` and
`0 < ε ≤ 1/2` (with the standing `ε⁻¹ ≤ n`), with `n₀ = n + vol_G(V)/d`, `m₀ = m + vol_G(V)` and
`L` given by (17) at ambient bounds `n̂ ≥ n₀`, `m̂ ≥ m₀`, one can construct a `(1 ± ε)`-spectral
sparsifier with `O(n₀ ϕ⁻² ε⁻² L)` edges (31); the sparse implementation takes
`O(m₀ + n₀ m₀ ϕ⁻³ ε^{-5/2} L³)` time (33), and for every achievable exponent `α > 2` the dense
implementation takes `O(m₀ + (n₀^α log n₀ + n₀² L^{O(1)} + m₀) ϕ⁻² ε⁻² L)` time (32). -/
theorem lemma_12 :
    ∀ c₀ : ℝ, 0 < c₀ →
    (∃ (P : Program) (K : ℕ) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (d ϕ ε : ℝ) (nh mh : ℕ),
        G.NonloopWeightsIn 1 2 → G.LoopsNonneg → 0 < ϕ → G.CondAtLeast ϕ → 1 ≤ d →
        (∀ v, c₀ * d ≤ G.deg v) → 0 < ε → ε ≤ 1 / 2 → ε⁻¹ ≤ n →
        (n : ℝ) + G.vol Finset.univ / d ≤ nh → (G.m : ℝ) + G.vol Finset.univ ≤ mh →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m + nh + mh) (graphInput G [nh, mh] [ε, d, ϕ]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          let n₀ : ℝ := n + G.vol Finset.univ / d
          let m₀ : ℝ := G.m + G.vol Finset.univ
          let L : ℝ := max 2 (Real.log (64 * ((nh : ℝ) + mh) ^ 4 / (ε * ϕ)))
          (H.m : ℝ) ≤ C * n₀ * ϕ⁻¹ ^ 2 * (ε ^ 2)⁻¹ * L ∧
          (T : ℝ) ≤ C * (m₀ + n₀ * m₀ * ϕ⁻¹ ^ 3 * ε ^ (-(5 / 2 : ℝ)) * L ^ 3)) ∧
    ∀ α : ℝ, 2 < α → Achievable α →
    ∃ (P : Program) (K κ : ℕ) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (d ϕ ε : ℝ) (nh mh : ℕ),
        G.NonloopWeightsIn 1 2 → G.LoopsNonneg → 0 < ϕ → G.CondAtLeast ϕ → 1 ≤ d →
        (∀ v, c₀ * d ≤ G.deg v) → 0 < ε → ε ≤ 1 / 2 → ε⁻¹ ≤ n →
        (n : ℝ) + G.vol Finset.univ / d ≤ nh → (G.m : ℝ) + G.vol Finset.univ ≤ mh →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m + nh + mh) (graphInput G [nh, mh] [ε, d, ϕ]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          let n₀ : ℝ := n + G.vol Finset.univ / d
          let m₀ : ℝ := G.m + G.vol Finset.univ
          let L : ℝ := max 2 (Real.log (64 * ((nh : ℝ) + mh) ^ 4 / (ε * ϕ)))
          (H.m : ℝ) ≤ C * n₀ * ϕ⁻¹ ^ 2 * (ε ^ 2)⁻¹ * L ∧
          (T : ℝ) ≤ C * (m₀ + (n₀ ^ α * Real.log n₀ + n₀ ^ 2 * L ^ κ + m₀) *
            ϕ⁻¹ ^ 2 * (ε ^ 2)⁻¹ * L) := by sorry

end DetSpectralSparsify.Dense
