-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_10
-- name    : CompactRouting.Labeled.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:38.662746+00:00
-- url     : https://prove2.me/theorems/598aec14-238c-451c-8f9e-4f44a8f0ed4b
-- title:
--   Lemma 10 — the value of the level LP is at most $2\tau$
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. Fix a source $u$ and a destination $v\neq u$ with $v\notin B(u)\cup C(u)$ (§4.2), let $\tau=\min\{i\in[k] : p_i(v)\in B(u)\}$ be the fallback level, and $$M=\max\Big\{h_1(v),\ \max_{0\le i<\tau}\big(h_{i+1}(u)-h_i(v)\big),\ \max_{1\le i\le\tau}|h_i(u)-h_i(v)|\Big\}$$ (§4.3). Let $z^*$ be the value of the linear program (3). Then
--   $$z^*\le2\tau.$$
--   With Lemma 9 and $\tau\le k-1$ this gives expected stretch $1+2\tau\le2k-1$.
--
--   Differences from the source:
--   - encoding: z* = min{z | …} → `lpValue`, the real infimum of the feasible values; reason: the feasible set is nonempty, closed and bounded below by 0 (M > 0 by (1)), so the infimum is the minimum
--   - encoding: §4.2–4.3 standing assumptions 'fix u, v ≠ u with v ∉ B(u) ∪ C(u)', τ = min{i ∈ [k] | p_i(v) ∈ B(u)}, M = max{…} → hypotheses `u ≠ v`, `v ∉ bunch A u`, `v ∉ cluster A u`, `IsFallbackLevel A p u v τ` (the characterization of the minimum), `lowerM` (maximum of a finite nonempty set); reason: Lean convention; same instances
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 14, Lemma 10 (proof in §B.1, p. 36)

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_LevelLP

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 14, Lemma 10 (proved in §B.1, p. 36): "z∗ ≤ 2τ."
`z*` is the value of the LP (3) (`lpValue`), under the standing assumptions of §4.2 as in (1). -/
theorem lemma_10 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (hp : IsPivots A p)
    (u v : Fin G.n) (huv : u ≠ v) (hB : v ∉ bunch A u) (hCu : v ∉ cluster A u)
    (τ : ℕ) (hτ : IsFallbackLevel A p u v τ) :
    lpValue A u v τ ≤ 2 * (τ : ℝ) := by sorry

end CompactRouting.Labeled
