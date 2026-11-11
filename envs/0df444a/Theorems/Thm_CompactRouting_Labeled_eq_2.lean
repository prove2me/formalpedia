-- Prove2me | Theorems.Thm_CompactRouting_Labeled_eq_2
-- name    : CompactRouting.Labeled.eq_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:47.428463+00:00
-- url     : https://prove2.me/theorems/20550fbb-3e16-4749-94b9-863ba4cc983d
-- title:
--   §4.3, (2) — route length of Algorithm 1 for a chosen level $i\in[\tau]$
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. Fix a source $u$ and a destination $v\neq u$ with $v\notin B(u)\cup C(u)$ (§4.2), let $\tau=\min\{i\in[k] : p_i(v)\in B(u)\}$ be the fallback level, and $$M=\max\Big\{h_1(v),\ \max_{0\le i<\tau}\big(h_{i+1}(u)-h_i(v)\big),\ \max_{1\le i\le\tau}|h_i(u)-h_i(v)|\Big\}$$ (§4.3). If the source chooses the level $i\in[\tau]$, the route of Algorithm 1 satisfies
--   $$\hat d(u,v)\le \mathrm{route}_i\le d(u,v)+2h_i(u)+2h_\tau(v)\cdot\mathbf 1\big[d(u,v)\ge h_{i+1}(v)-h_i(u)\big],\tag{2}$$
--   where $\mathrm{route}_i$ is the length of Algorithm 1's legs with the fallback leg $u\rightsquigarrow v$ in $T(C(p_\tau(v)))$ measured through the root $p_\tau(v)$ (`levelRoute`); the Lean statement is the second inequality.
--
--   Differences from the source:
--   - generalization: d̂(u, v), the length of the walk along the cluster-tree paths, stopped at its first arrival at v → `levelRoute`, the length of the legs u ⇝ p_i(u) ⇝ v, or u ⇝ p_i(u) ⇝ u ⇝ p_τ(v) ⇝ v through the root of each tree; reason: legs from and to the root of a shortest-path tree have exactly these lengths and the tree path u ⇝ v is at most the walk through the root, so levelRoute ≥ d̂ and the Lean bound implies (2)
--   - encoding: §4.2–4.3 standing assumptions 'fix u, v ≠ u with v ∉ B(u) ∪ C(u)', τ = min{i ∈ [k] | p_i(v) ∈ B(u)}, M = max{…} → hypotheses `u ≠ v`, `v ∉ bunch A u`, `v ∉ cluster A u`, `IsFallbackLevel A p u v τ` (the characterization of the minimum), `lowerM` (maximum of a finite nonempty set); reason: Lean convention; same instances
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 13, §4.3, (2)

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_LevelLP

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 13, §4.3, (2): "If the source chooses i ∈ [τ], then
d̂(u, v) ≤ d(u, v) + 2h_i(u) + 2h_τ(v) · 1[d(u, v) ≥ h_{i+1}(v) − h_i(u)]."
Standing assumptions of §4.2 as in (1). `levelRoute A p u v τ i` is the length of Algorithm 1's
route for level `i`, with the fallback leg measured through the root `p_τ(v)` of its cluster tree
(at least the walk's length `d̂(u, v)`). -/
theorem eq_2 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (hp : IsPivots A p)
    (u v : Fin G.n) (huv : u ≠ v) (hB : v ∉ bunch A u) (hCu : v ∉ cluster A u)
    (τ : ℕ) (hτ : IsFallbackLevel A p u v τ) :
    ∀ i < τ, levelRoute A p u v τ i ≤
      dist G u v + 2 * height A i u +
        2 * height A τ v * (if height A (i + 1) v - height A i u ≤ dist G u v then 1 else 0) := by sorry

end CompactRouting.Labeled
