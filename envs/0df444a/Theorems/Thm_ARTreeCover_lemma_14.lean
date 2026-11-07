-- Prove2me | Theorems.Thm_ARTreeCover_lemma_14
-- name    : ARTreeCover.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:57:58.877303+00:00
-- url     : https://prove2.me/theorems/2f310c83-a4e7-4e66-bf34-c237549e068b
-- title:
--   Lemma 14: layered covers of all minors give covers of size $s\cdot O(\log n/\epsilon)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $\alpha\ge 1$, $0<\epsilon\le 1$ and $s$ a natural number. Suppose that for every $\Delta>0$ every minor of $G$ has an $s$-layered $(\Delta,\alpha)$-pairwise cover. Then $G$ has a forest cover and an HST cover, each of size at most $C\,s\,\epsilon^{-1}L(n)$ and stretch $(2+\epsilon)\alpha$, such that
--
--   1. if all these pairwise covers are strong, the forest cover is spanning;
--   2. if all these pairwise covers are $(\Delta,\alpha)$-neighborhood covers, the forest cover and the HST cover are almost-Ramsey with stretch $(2+\epsilon)\alpha$.
--
--   This reduces tree covers to layered clusterings of minors. Since the minors of a graph are graphs, Theorem 13 and Theorem 11, Item 1 apply to every minor, and the goal follows.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log n in the size bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, while a one-vertex graph needs at least one forest or layer for the pair (u, u)
--   - reading: s(ϵ) in the hypothesis and s(ϵ/5, n) in the size bound → a fixed natural number `s` in both; reason: the printed form is the instance with the value of the function at the smaller parameter, and a fixed bound is a constant function; n is fixed with G
--   - reading: the "moreover" clauses, each about the cover F → Boolean flags in the hypothesis and the conclusion; one cover carries every clause whose flag is set; reason: the printed clauses are about the same F, and Theorem 19 needs a spanning almost-Ramsey forest cover
--   - reading: every minor G∗ of G (vertex deletions, edge deletions, edge contractions; p.9) → a branch-set minor H on any finite vertex type, each edge of H carrying the weight of a G-edge between its branch sets; reason: a contraction merges parallel edges by keeping one, and earlier deletions choose which; conversely every such choice arises by deleting the others; Appendix A uses exactly these minors
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: an s-layered clustering C = Π₁ ∪ … ∪ Π_s (Definition 1) → a family of s partitions of V (`Fin s → Finpartition univ`), repetitions allowed; reason: the clusters are the parts; a clustering with fewer layers is s-layered by repeating a layer
--   - encoding: forests with V(F) ⊆ V and weights in (0, ∞] → a forest on all of V; a vertex outside V(F) is isolated; reason: this changes no distance between distinct vertices and gives d_F(u, u) = 0, which the paper assumes (p.31)
--   - reading: spanning: E(F) ⊆ E → every edge of F is an edge of G and carries G's weight; reason: a forest whose edges are edges of G but with other weights is not a subgraph of the weighted graph G
--   - encoding: an HST is a rooted tree with labels (Definition 3) → the leaf set L(T) with the ultrametric ρ_T(x, y) = ℓ(LCA(x, y)), and ρ_T = ∞ off the leaves; reason: by the paper's sentence after Definition 3 and Fact 6 the leaf ultrametrics of HSTs are exactly the finite ultrametrics, and no statement uses the internal vertices; ∞ off the leaves lets d_G ≤ ρ_T be stated for all pairs of V
--   - reading: HST labels in ℝ≥0 (Definition 3) → ρ_T takes values in [0, ∞]; reason: the proof of Lemma 13 labels a root "diam(G) or ∞" (p.32); with finite labels the HST clauses fail on edgeless graphs, where d_G(u, v) = ∞ forces one leaf per HST and n HSTs
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Lemma 14, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WMinor
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover
import Definitions.Def_ARTreeCover_IsPairwiseCover

namespace ARTreeCover

/-- **Lemma 14**, p.33 (PDF p.36). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex graph and let α ≥ 1 and 0 < ϵ ≤ 1 be some real parameters
parameters. Suppose that for any ∆ > 0, every minor G∗ of G admits an s-layered (∆, α)-pairwise
cover C∗_∆, where s = s(ϵ, n). Then, G admits a forest cover F and a HST cover H, both with stretch
at most (2 + ϵ)α and size at most s(ϵ/5, n) · O(log n/ϵ), such that 1. if for every ∆ > 0 and
every minor G∗, C∗_∆ is a strong pairwise cover, then F is a spanning forest cover. 2. if for every
∆ > 0 and every minor G∗, C∗_∆ is a (∆, α)-neighborhood cover, then F is an almost-Ramsey forest
cover and H is an almost-Ramsey HST cover, both with stretch (2+ϵ)α."

**Formalization Note.**
1. Minors are weighted minors on any finite type with decidable equality (`WMinor`).
2. The layer count `s(·, n)` is a fixed natural number `s` (for this `G`, so `n` is fixed); the
   size is `C · s · ϵ⁻¹ · L(n)` with one absolute `C > 0` chosen before everything else.
3. `strong = true` adds "strong" to the hypothesis (`false`: weak covers), `nbhd = true` adds
   the neighborhood property; one `F` and one `H` carry every applicable item. The weak case of
   `lemma_13` needs `2s` forests instead of `s`; the absolute constant `C` absorbs the factor. -/
theorem lemma_14 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (ε α : ℝ) (s : ℕ)
        (strong nbhd : Bool),
        1 ≤ α → 0 < ε → ε ≤ 1 →
        (∀ Δ : ℝ, 0 < Δ → ∀ (W : Type) [Fintype W] [DecidableEq W] (H : WGraph W), WMinor H G →
          ∃ Pi : Fin s → Finpartition (Finset.univ : Finset W),
            IsPairwiseCover H strong Δ α Pi ∧
            (nbhd = true → IsNeighborhoodCover H strong Δ α Pi)) →
        (∃ m : ℕ, (m : ℝ) ≤ C * s * ε⁻¹ * logL (Fintype.card V) ∧
          ∃ F : Fin m → WForest V,
            IsForestCover G F ∧ ForestStretchLE G F ((2 + ε) * α) ∧
            (strong = true → ∀ i, (F i).IsSpanning G) ∧
            (nbhd = true → ForestAlmostRamsey G F ((2 + ε) * α))) ∧
        (∃ m : ℕ, (m : ℝ) ≤ C * s * ε⁻¹ * logL (Fintype.card V) ∧
          ∃ T : Fin m → HST V,
            IsHSTCover G T ∧ HSTStretchLE G T ((2 + ε) * α) ∧
            (nbhd = true → HSTAlmostRamsey G T ((2 + ε) * α))) := by sorry

end ARTreeCover
