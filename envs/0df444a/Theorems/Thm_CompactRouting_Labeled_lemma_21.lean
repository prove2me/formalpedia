-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_21
-- name    : CompactRouting.Labeled.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:40.849592+00:00
-- url     : https://prove2.me/theorems/65ebe6c2-c0ed-49c2-9767-5433360d7916
-- title:
--   Lemma 21 — properties (N1)–(N4) of the normalized heights
-- statement:
--   Throughout, $G$ is a connected simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ with positive edge weights, $d(u,v)$ its shortest-path distance, $k\ge 2$ an integer, $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ a hierarchy with $A_{k-1}\neq\emptyset$, $h_i(x)=d(x,A_i)$ the heights, $p_i(x)$ pivots chosen by the paper's rule ($p_{k-1}(x)$ a closest vertex of $A_{k-1}$; for $i<k-1$, $p_i(x)=p_{i+1}(x)$ if $h_i(x)=h_{i+1}(x)$ and otherwise a closest vertex of $A_i$), $B(x)$ the bunch and $C(w)$ the cluster of §2.1. Fix a source $u$ and a destination $v\neq u$ with $v\notin B(u)\cup C(u)$ (§4.2), let $\tau=\min\{i\in[k] : p_i(v)\in B(u)\}$ be the fallback level, and $$M=\max\Big\{h_1(v),\ \max_{0\le i<\tau}\big(h_{i+1}(u)-h_i(v)\big),\ \max_{1\le i\le\tau}|h_i(u)-h_i(v)|\Big\}$$ (§4.3). Put $x_i=h_i(u)/M$, $y_i=h_i(v)/M$ ($0\le i\le\tau$) and $H=y_\tau$. Then $x$ and $y$ are nondecreasing on $0,\dots,\tau$, $x_0=y_0=0$, $0<H\le2\tau-1$, and
--   $$x_1\le1,\ y_1\le1\ \text{(N1)},\quad x_{i+1}\le y_i+1\ (0\le i<\tau)\ \text{(N2)},\quad |x_i-y_i|\le1\ (0\le i\le\tau)\ \text{(N3)},\quad 0\le y_{i+1}-y_i\le2\ (0\le i<\tau)\ \text{(N4)}.$$
--   These are the only facts about the graph that the optimization bounds of Appendix B use.
--
--   Differences from the source:
--   - encoding: the list of properties → the structure `NormalizedHeights x y τ`, one field per property, sequences indexed by ℕ and used for 0 ≤ i ≤ τ; reason: Lean convention; same content
--   - encoding: §4.2–4.3 standing assumptions 'fix u, v ≠ u with v ∉ B(u) ∪ C(u)', τ = min{i ∈ [k] | p_i(v) ∈ B(u)}, M = max{…} → hypotheses `u ≠ v`, `v ∉ bunch A u`, `v ∉ cluster A u`, `IsFallbackLevel A p u v τ` (the characterization of the minimum), `lowerM` (maximum of a finite nonempty set); reason: Lean convention; same instances
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 35, Lemma 21

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_LevelLP

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 35, Lemma 21: "The normalized heights are nondecreasing,
x_0 = y_0 = 0, 0 < H ≤ 2τ − 1, and x_1 ≤ 1 and y_1 ≤ 1 (N1), x_{i+1} ≤ y_i + 1 (0 ≤ i < τ) (N2),
|x_i − y_i| ≤ 1 (0 ≤ i ≤ τ) (N3), 0 ≤ y_{i+1} − y_i ≤ 2 (0 ≤ i < τ) (N4)."
Here `x_i = h_i(u)/M`, `y_i = h_i(v)/M` (`0 ≤ i ≤ τ`), `H = y_τ`, under the standing
assumptions of §4.2 and §4.3 ("Fix u, v, τ, and M as in Section 4.3", p. 35). -/
theorem lemma_21 (G : Graph) (hS : IsSimple G) (hW : G.PosWeights) (hC : G.Connected)
    (k : ℕ) (hk : 2 ≤ k) (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (hp : IsPivots A p)
    (u v : Fin G.n) (huv : u ≠ v) (hB : v ∉ bunch A u) (hCu : v ∉ cluster A u)
    (τ : ℕ) (hτ : IsFallbackLevel A p u v τ) :
    NormalizedHeights (fun i => height A i u / lowerM A u v τ)
      (fun i => height A i v / lowerM A u v τ) τ := by sorry

end CompactRouting.Labeled
