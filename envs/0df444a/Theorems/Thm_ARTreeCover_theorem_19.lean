-- Prove2me | Theorems.Thm_ARTreeCover_theorem_19
-- name    : ARTreeCover.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:19.222821+00:00
-- url     : https://prove2.me/theorems/791632df-1a91-4c50-bcdb-806b4200dc3a
-- title:
--   Theorem 19: (almost-Ramsey) spanning tree covers of general graphs
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $k>0$ an integer and $0<\epsilon\le 1$. With $L(n)=\max(1,\log_2 n)$ and
--
--   $$A=C\,\epsilon^{-1}n^{1/k}L(n)^2,\qquad B=C\,\epsilon^{-1}k\,n^{1/k}L(n),$$
--
--   the graph $G$ admits:
--
--   1. a spanning forest cover of size at most $A$ and stretch at most $(2+\epsilon)k$;
--   2. an HST cover of size at most $A$ and stretch at most $(2+\epsilon)k$;
--   3. a spanning almost-Ramsey forest cover of size at most $B$ and stretch at most $(4k-2)(1+\epsilon)$;
--   4. an almost-Ramsey HST cover of size at most $B$ and stretch at most $(4k-2)(1+\epsilon)$.
--
--   If $G$ is connected, then the covers of items 1 and 3 can be taken to consist of spanning trees of $G$, with the same stretch and size.
--
--   This removes the $O(\log\log n)$ factor of the Ramsey spanning tree covers of Abraham et al. (2020) at a polylogarithmic cost in size, and the stretch $(2+\epsilon)k$ is within a factor $1+o(1)$ of twice the lower bound $2k-1$ that follows from the Erdős girth conjecture.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log n in the size bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, while a one-vertex graph needs at least one forest or layer for the pair (u, u)
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: forests with V(F) ⊆ V and weights in (0, ∞] → a forest on all of V; a vertex outside V(F) is isolated; reason: this changes no distance between distinct vertices and gives d_F(u, u) = 0, which the paper assumes (p.31)
--   - reading: spanning: E(F) ⊆ E → every edge of F is an edge of G and carries G's weight; reason: a forest whose edges are edges of G but with other weights is not a subgraph of the weighted graph G
--   - encoding: an HST is a rooted tree with labels (Definition 3) → the leaf set L(T) with the ultrametric ρ_T(x, y) = ℓ(LCA(x, y)), and ρ_T = ∞ off the leaves; reason: by the paper's sentence after Definition 3 and Fact 6 the leaf ultrametrics of HSTs are exactly the finite ultrametrics, and no statement uses the internal vertices; ∞ off the leaves lets d_G ≤ ρ_T be stated for all pairs of V
--   - reading: HST labels in ℝ≥0 (Definition 3) → ρ_T takes values in [0, ∞]; reason: the proof of Lemma 13 labels a root "diam(G) or ∞" (p.32); with finite labels the HST clauses fail on edgeless graphs, where d_G(u, v) = ∞ forces one leaf per HST and n HSTs
--   - encoding: "with the same stretch and size as F and F′" → the bounds A and B, the stretches (2+ϵ)k and (4k−2)(1+ϵ); the trees are `SimpleGraph.IsTree` on all of V; reason: "spanning tree cover" means spanning trees of G (§1, p.1)
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 19, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WMinor
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover

namespace ARTreeCover

/-- **Theorem 19**, p.33 (PDF p.36). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let k > 0 be an integer parameter and let 0 < ϵ ≤ 1 be a real parameter. Any n-vertex undirected
weighted graph G admits a spanning forest cover F and a HST cover H, both with stretch at most
(2 + ϵ)k and size at most O(1/ϵ n^{1/k} · log² n). In addition, the graph G admits a spanning
almost-Ramsey forest cover F′ and an almost-Ramsey HST cover H′, both with stretch at most
(4k − 2)(1 + ϵ) and size at most O(1/ϵ kn^{1/k} · log n). If G is connected, then by Observation
1, there is a spanning tree cover T and a spanning almost-Ramsey tree cover T′ with the same
stretch and size as F and F′, respectively."

With `n = |V|`, `L(n) = max(1, log₂ n)`, `A = C ϵ⁻¹ n^{1/k} L(n)²` and `B = C ϵ⁻¹ k n^{1/k} L(n)`:
1. a spanning forest cover of size ≤ `A` with stretch `(2+ϵ)k`;
2. an HST cover of size ≤ `A` with stretch `(2+ϵ)k`;
3. a spanning almost-Ramsey forest cover of size ≤ `B` with stretch `(4k−2)(1+ϵ)`;
4. an almost-Ramsey HST cover of size ≤ `B` with stretch `(4k−2)(1+ϵ)`;
5. if `G` is connected, the covers of 1 and 3 can be taken to consist of spanning trees of `G`.

**Formalization Note.**
1. One absolute constant `C > 0` is chosen before `V`, `G`, `k` and `ϵ` (the paper's O(·)).
2. `G` is any finite weighted graph with positive weights, connected or not; `d_G`, forest
   distances and HST labels take values in `[0, ∞]` (forest edges outside `G` may weigh `∞`,
   footnote 13; HST labels may be `∞`, as in Lemma 13's proof).
3. Forests are on all of `V`; spanning means edges of `G` with `G`'s weights; HSTs are leaf
   ultrametrics (Definition 3, Fact 6).
4. Almost-Ramsey covers are also stated with stretch, which almost-Ramsey implies. -/
theorem theorem_19 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (k : ℕ) (ε : ℝ), 0 < k → 0 < ε → ε ≤ 1 →
        let n : ℝ := Fintype.card V
        let A : ℝ := C * ε⁻¹ * n ^ ((1 : ℝ) / k) * logL n ^ 2
        let B : ℝ := C * ε⁻¹ * k * n ^ ((1 : ℝ) / k) * logL n
        (∃ m : ℕ, (m : ℝ) ≤ A ∧ ∃ F : Fin m → WForest V,
          (∀ i, (F i).IsSpanning G) ∧ IsForestCover G F ∧ ForestStretchLE G F ((2 + ε) * k)) ∧
        (∃ m : ℕ, (m : ℝ) ≤ A ∧ ∃ T : Fin m → HST V,
          IsHSTCover G T ∧ HSTStretchLE G T ((2 + ε) * k)) ∧
        (∃ m : ℕ, (m : ℝ) ≤ B ∧ ∃ F : Fin m → WForest V,
          (∀ i, (F i).IsSpanning G) ∧ IsForestCover G F ∧
          ForestStretchLE G F ((4 * k - 2) * (1 + ε)) ∧
          ForestAlmostRamsey G F ((4 * k - 2) * (1 + ε))) ∧
        (∃ m : ℕ, (m : ℝ) ≤ B ∧ ∃ T : Fin m → HST V,
          IsHSTCover G T ∧ HSTStretchLE G T ((4 * k - 2) * (1 + ε)) ∧
          HSTAlmostRamsey G T ((4 * k - 2) * (1 + ε))) ∧
        (G.graph.Connected →
          (∃ m : ℕ, (m : ℝ) ≤ A ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).graph.IsTree ∧ (T i).IsSpanning G) ∧ IsForestCover G T ∧
            ForestStretchLE G T ((2 + ε) * k)) ∧
          (∃ m : ℕ, (m : ℝ) ≤ B ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).graph.IsTree ∧ (T i).IsSpanning G) ∧ IsForestCover G T ∧
            ForestStretchLE G T ((4 * k - 2) * (1 + ε)) ∧
            ForestAlmostRamsey G T ((4 * k - 2) * (1 + ε)))) := by sorry

end ARTreeCover
