-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_5
-- name    : CompactRouting.Labeled.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:06:52.913686+00:00
-- url     : https://prove2.me/theorems/726f2ef6-420c-4ac6-aefd-31ab8df61cec
-- title:
--   Lemma 5 — $h_{i+1}(v)>d(u,v)+h_i(u)$ puts $v$ in the cluster of $p_i(u)$
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. For every $i\in[k]$ and $u,v\in V$,
--   $$h_{i+1}(v)>d(u,v)+h_i(u)\ \Longrightarrow\ v\in C(p_i(u)),$$
--   where $h_k(v)=d(v,\emptyset)=\infty$. This is what bounds the cost of a failed pivot visit in the route-length bound (2).
--
--   Differences from the source:
--   - reading: 'If h_{i+1}(v) > d(u, v) + h_i(u)' with no range for i → every i ∈ [k], with h_k(v) = ∞ (comparison in WithTop ℝ); reason: i ∈ [k] is the paper's index range for pivots
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 6, Lemma 5

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_Clusters

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 6, Lemma 5 (Lemma 16 of [KR25a]):
"If h_{i+1}(v) > d(u, v) + h_i(u), then v ∈ C(p_i(u))." Here `i ∈ [k]`, and
`h_{i+1}(v) = d(v, A_{i+1})` is compared in `WithTop ℝ` (it is `∞` for `i = k − 1`). -/
theorem lemma_5 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (hp : IsPivots A p) :
    ∀ i < k, ∀ u v : Fin G.n,
      (((dist G u v + height A i u : ℝ)) : WithTop ℝ) < distToSet G (A.A (i + 1)) v →
        v ∈ cluster A (p i u) := by sorry

end CompactRouting.Labeled
