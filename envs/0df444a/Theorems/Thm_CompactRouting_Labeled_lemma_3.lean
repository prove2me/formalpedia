-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_3
-- name    : CompactRouting.Labeled.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:06:37.939051+00:00
-- url     : https://prove2.me/theorems/0fd1661a-6495-4902-89ff-e68bb6e3930c
-- title:
--   Lemma 3 — every pivot of $u$ lies in $B(u)$, and $u$ lies in its pivot's cluster
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. For every $u\in V$ and $i\in[k]$,
--   $$p_i(u)\in B(u)\quad\text{and}\quad u\in C(p_i(u)).$$
--   This is why a message can always be sent from the source to any of its own pivots inside that pivot's cluster tree.
--
--   Differences from the source:
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 6, Lemma 3

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_Clusters

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 6, Lemma 3 (Lemma 4.1 of [TZ05]):
"For every u ∈ V and i ∈ [k], p_i(u) ∈ B(u) and u ∈ C(p_i(u))." -/
theorem lemma_3 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (hp : IsPivots A p) :
    ∀ u : Fin G.n, ∀ i < k, p i u ∈ bunch A u ∧ u ∈ cluster A (p i u) := by sorry

end CompactRouting.Labeled
