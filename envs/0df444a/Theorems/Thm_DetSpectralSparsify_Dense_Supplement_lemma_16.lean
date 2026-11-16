-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_Supplement_lemma_16
-- name    : DetSpectralSparsify.Dense.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:47.70204+00:00
-- url     : https://prove2.me/theorems/12d38e3f-91c5-4d0a-8d85-780ee70f3a86
-- title:
--   Lemma 16 (Weight spread) — Algorithm 8 output weights, after aggregation, have ratio at most $2^{b+O(\log n)}$
-- statement:
--   Fix implementation data of Algorithms 4–6 meeting their specification, a conductance sequence $\phi_n=\log^{-9-o(1)}n$, a mode (dense or sparse) and an exponent $c$. There is a constant $C>0$ such that the following holds. Let $N$ be a size bound and $G$ a positively weighted multigraph with $n\le N$ vertices and $m$ edges, let $0<\varepsilon\le1/2$ with $m,\varepsilon^{-1}\le N^c$, and let $b$ be a real number such that any two non-loop edges $e,f$ of $G$ satisfy $w(e)<2^b\,w(f)$. Then for every output $H$ of a run of Algorithm 8 (WeightedSparsify) on $(G,\varepsilon)$ in this mode, the aggregated graph $\bar H$ satisfies
--
--   $$w_{\bar H}(e)\;\le\;2^{\,b+C\ln N}\,w_{\bar H}(f)\qquad\text{for all edges }e,f\text{ of }\bar H .$$
--
--   In words: the ratio between the largest and smallest output edge weights after aggregating parallel edges is at most $2^{b+O(\log N)}$ (in particular $2^{b+O(\log n)}$ when $N=n$), with the $O$-constant depending only on $c$, the implementation data and the sequence $\phi$. The recursive analysis of Theorem 17 uses this to control the growth of the dyadic weight range from level to level.
--
--   **Formalization Note** Algorithm 8 is the execution relation `WeightedSparsify`; the statement covers every run. The ratio condition is written pairwise, so an empty edge list makes the hypothesis or the conclusion vacuous, and no maximum or minimum of an empty set occurs.
--
--   Differences from the source:
--   - generalization: the dense or sparse weighted sparsification algorithm with its fixed choices → every run of the execution relation, for all implementation data meeting the structural specification (any tie and removal order, Euler tour, greedy order, expander decomposition meeting Theorem 13's guarantees, constants a ≥ 1, C₀ > 0, c > 0 and any constant-degree constant-conductance expander family); reason: every fixed implementation is one run, so the statement specializes to it
--   - generalization: the dense (§4.1) and sparse (§4.3) score evaluations → any scores within the Lemma 6 tolerance R/(16εk); reason: both evaluations are shown (pp.12–17) to produce such scores, so their runs are included
--   - generalization: conductance lower bound ϕ_n → every sequence ϕ with ϕ_n ∈ (0,1] and ϕ_n⁻¹ = log^{9+h(n)} n, h → 0; reason: the pinned sequence is one of them
--   - generalization: ratio between the largest and smallest input edge weights less than 2^b, b an integer → the same condition on non-loop edges only, b any real; reason: Algorithm 8 discards self-loops, and every source instance satisfies the weaker hypothesis
--   - generalization: standing assumptions ε⁻¹ ≤ n and no isolated vertices (p.5) → ε⁻¹ ≤ n^c as in the lemma, isolated vertices allowed; reason: the lemma itself assumes only ε⁻¹ ≤ n^{O(1)}, and Theorem 17 applies Algorithm 8 to graphs J̄ that may have isolated vertices
--   - generalization: size bounds n, m with m, ε⁻¹ ≤ n^{O(1)} and ratio 2^{b+O(log n)} → any N ≥ |V(G)| with m, ε⁻¹ ≤ N^c and ratio 2^{b+C ln N}; reason: the lemma's "size bounds" may be read as exact sizes or as ambient upper bounds; the Lean covers both, and N = |V(G)| gives the exact-size reading
--   - reading: Theorem 13 applied to F[U] gives conductance ϕ_n → the decomposition of Algorithm 7 meets ϕ_n with n the number of vertices of Algorithm 7's input; reason: Algorithm 7 line 11 uses that same ϕ_n for every cluster
--   - encoding: ratio at most 2^{b+O(log n)} → for all aggregated output edges e, f, w(e) ≤ 2^{b+C ln N} w(f), with C chosen before the instance; reason: pairwise form of the ratio for positive weights
--   - encoding: operators on U = (D^{1/2}𝟏)^⊥ → zero-extended matrices on ℝ^N, P as the functional calculus of x ↦ x^{-1/2} with value 0 at 0; reason: the traces in Algorithm 1 are unchanged
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.27, Lemma 16 (proof p.28); Algorithm 8 p.27, Algorithms 2, 4–7 pp.10–23

import Definitions.Def_DetSpectralSparsify_Dense_Supplement_WeightedSparsify

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense.Supplement

open DetSpectralSparsify.Dense

/-- Lemma 16 (Weight spread), p.27 (proof p.28). For every choice of the implementation data of
Algorithms 4–6 meeting their specification, every conductance sequence `ϕ_n = log^{-9-o(1)} n`,
either mode, and every polynomial regime `m, ε⁻¹ ≤ N^c`, there is `C` such that: for every size
bound `N` and every positively weighted multigraph `G` with `n ≤ N` vertices and `m` edges and
accuracy `0 < ε ≤ 1/2` whose non-loop weights have ratio less than `2^b`, every output `H` of
Algorithm 8 (WeightedSparsify) has, after aggregating parallel edges, all weight ratios at most
`2^{b + C log N}`. At `N = n` this is the lemma with exact sizes. -/
theorem lemma_16 :
    ∀ D : ImplData, D.Spec → ∀ ϕ h : ℕ → ℝ, IsPhiSequence ϕ h → ∀ (mode : Mode) (c : ℕ),
    ∃ C : ℝ, 0 < C ∧
    ∀ (N n : ℕ) (G : Multigraph n) (ε b : ℝ),
      n ≤ N → G.PosWeights → 0 < ε → ε ≤ 1 / 2 →
      (G.m : ℝ) ≤ (N : ℝ) ^ c → ε⁻¹ ≤ (N : ℝ) ^ c →
      (∀ e f : Fin G.m, ¬ G.IsLoop e → ¬ G.IsLoop f → G.w e < (2 : ℝ) ^ b * G.w f) →
      ∀ H : Multigraph n, WeightedSparsify D ϕ G ε mode H →
        ∀ e f : Fin H.aggregate.m,
          H.aggregate.w e ≤ (2 : ℝ) ^ (b + C * Real.log N) * H.aggregate.w f := by sorry

end DetSpectralSparsify.Dense.Supplement
