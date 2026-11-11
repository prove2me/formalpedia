-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_9
-- name    : CompactRouting.Labeled.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:43.218547+00:00
-- url     : https://prove2.me/theorems/01c1218e-0fdb-4f37-895e-f43bf8164950
-- title:
--   Lemma 9 — expected route length at most $(1+z^*)\,d(u,v)$
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. Fix a source $u$ and a destination $v\neq u$ with $v\notin B(u)\cup C(u)$ (§4.2), let $\tau=\min\{i\in[k] : p_i(v)\in B(u)\}$ be the fallback level, and $$M=\max\Big\{h_1(v),\ \max_{0\le i<\tau}\big(h_{i+1}(u)-h_i(v)\big),\ \max_{1\le i\le\tau}|h_i(u)-h_i(v)|\Big\}$$ (§4.3). Let $(\pi,z)$ be feasible for the linear program (3) (for instance an optimum $(\pi^*,z^*)$), and let the source draw $i\in[\tau]$ with probability $\pi_i$. Then
--   $$\mathbb E_{i\sim\pi}\big[\mathrm{route}_i\big]=\sum_{i\in[\tau]}\pi_i\,\mathrm{route}_i\le(1+z)\,d(u,v),$$
--   and in particular $\mathbb E[\hat d(u,v)]\le(1+z^*)d(u,v)$.
--
--   Differences from the source:
--   - generalization: the optimum (π*, z*) of (3) and E[d̂(u, v)] → every feasible (π, z) of (3), and the expectation of `levelRoute` (≥ d̂); reason: the optimum is feasible and levelRoute ≥ d̂ (see (2)), so the statement specializes to Lemma 9
--   - encoding: §4.2–4.3 standing assumptions 'fix u, v ≠ u with v ∉ B(u) ∪ C(u)', τ = min{i ∈ [k] | p_i(v) ∈ B(u)}, M = max{…} → hypotheses `u ≠ v`, `v ∉ bunch A u`, `v ∉ cluster A u`, `IsFallbackLevel A p u v τ` (the characterization of the minimum), `lowerM` (maximum of a finite nonempty set); reason: Lean convention; same instances
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 14, Lemma 9

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_LevelLP

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 14, Lemma 9: "E[d̂(u, v)] ≤ (1 + z∗)d(u, v)."
Standing assumptions of §4.2 as in (1); the level `i` is drawn from the distribution `π` of any
feasible point `(π, z)` of the LP (3) (in particular an optimum `(π*, z*)`), and the route length
for level `i` is `levelRoute` (an upper bound on `d̂(u, v)`). -/
theorem lemma_9 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (hp : IsPivots A p)
    (u v : Fin G.n) (huv : u ≠ v) (hB : v ∉ bunch A u) (hCu : v ∉ cluster A u)
    (τ : ℕ) (hτ : IsFallbackLevel A p u v τ) :
    ∀ (π : ℕ → ℝ) (z : ℝ), LPFeasible A u v τ π z →
      ∑ i ∈ Finset.range τ, π i * levelRoute A p u v τ i ≤ (1 + z) * dist G u v := by sorry

end CompactRouting.Labeled
