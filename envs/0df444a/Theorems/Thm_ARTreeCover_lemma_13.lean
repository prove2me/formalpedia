-- Prove2me | Theorems.Thm_ARTreeCover_lemma_13
-- name    : ARTreeCover.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:38.060206+00:00
-- url     : https://prove2.me/theorems/cbbd332d-a4d0-4187-9817-025d2734b34b
-- title:
--   Lemma 13: a layered pairwise cover gives scale-$\Delta$ covers (corrected: weak forest covers have size at most $2s$)
-- statement:
--   Let $G$ be a weighted graph, $\Delta,\alpha>0$, and let $\Pi_1,\dots,\Pi_s$ be an $s$-layered strong (respectively, weak) $(\Delta,\alpha)$-pairwise cover of $G$. Then $G$ admits
--
--   1. a forest cover with scale-$\Delta$ stretch $2\alpha$, of size at most $s$ for a strong cover and at most $2s$ for a weak cover, which is spanning if the pairwise cover is strong;
--   2. an HST cover with scale-$\Delta$ stretch $2\alpha$ and size at most $s$;
--
--   and if the clustering is a $(\Delta,\alpha)$-neighborhood cover, both covers are Ramsey scale-$\Delta$ with stretch $2\alpha$.
--
--   This is the step from clusterings to trees: a shortest-path tree or a star on each cluster, and one forest or HST per layer.
--
--   Differences from the source:
--   - correction: F has size at most s for every pairwise cover, strong or weak → size at most s for a strong cover and at most 2s for a weak cover; the HST cover keeps s; reason: the printed proof says stars of one partition "can only share their roots", but a weak center q(C) may lie in another cluster of that partition. Counterexample with s = 1, ∆ = 1, α = 5/4: three 4-cycles D₀, D₁, D₂ with unit weights, a vertex c_i of D_{i+1} joined to all of D_i by edges of weight 5/4. {D₀, D₁, D₂} with centers c_i is a weak (1, 5/4)-neighborhood cover, and an exhaustive search finds no single dominating forest with d_F ≤ 5/2 on all cycle edges. With 2s the construction works: move one cluster of each cycle of length at least 3 of the map C ↦ (cluster of q(C)) to a second forest
--   - generalization: Definition 16 asks α ≥ 1 for a scale-∆ cover with stretch α → any α > 0 (the range of Definition 11); reason: the printed lemma starts from a pairwise cover with α > 0; for 2α ≥ 1 this is the printed claim, and the construction needs no lower bound
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: an s-layered clustering C = Π₁ ∪ … ∪ Π_s (Definition 1) → a family of s partitions of V (`Fin s → Finpartition univ`), repetitions allowed; reason: the clusters are the parts; a clustering with fewer layers is s-layered by repeating a layer
--   - encoding: forests with V(F) ⊆ V and weights in (0, ∞] → a forest on all of V; a vertex outside V(F) is isolated; reason: this changes no distance between distinct vertices and gives d_F(u, u) = 0, which the paper assumes (p.31)
--   - reading: spanning: E(F) ⊆ E → every edge of F is an edge of G and carries G's weight; reason: a forest whose edges are edges of G but with other weights is not a subgraph of the weighted graph G
--   - encoding: an HST is a rooted tree with labels (Definition 3) → the leaf set L(T) with the ultrametric ρ_T(x, y) = ℓ(LCA(x, y)), and ρ_T = ∞ off the leaves; reason: by the paper's sentence after Definition 3 and Fact 6 the leaf ultrametrics of HSTs are exactly the finite ultrametrics, and no statement uses the internal vertices; ∞ off the leaves lets d_G ≤ ρ_T be stated for all pairs of V
--   - reading: HST labels in ℝ≥0 (Definition 3) → ρ_T takes values in [0, ∞]; reason: the proof of Lemma 13 labels a root "diam(G) or ∞" (p.32); with finite labels the HST clauses fail on edgeless graphs, where d_G(u, v) = ∞ forces one leaf per HST and n HSTs
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Lemma 13, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover
import Definitions.Def_ARTreeCover_IsPairwiseCover

namespace ARTreeCover

/-- **Lemma 13**, p.32 (PDF p.35). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let C be an s-layered (∆, α)-pairwise cover of a graph G = (V, E). Then, G admits a scale-∆
forest cover F and a scale-∆ HST cover H, both with stretch at most 2α and size at most s, such
that 1. if C is a strong pairwise cover, then F is a spanning forest cover. 2. if C is a
(∆, α)-neighborhood cover, then F is a Ramsey scale-∆ forest cover and H is a Ramsey scale-∆ HST
cover, both with stretch 2α."

**Correction (weak covers only).** For a weak cover the forest cover has size at most `2s`, not
`s`. The proof (p.32) says the stars of the clusters of one partition "can only share their roots",
but a center `q(C)` outside `C` may lie in another cluster of the same partition, and centers can
form a cycle. Counterexample to size `s` with `s = 1`, `∆ = 1`, `α = 5/4`: three 4-cycles `D₀, D₁, D₂`
with unit weights, one vertex `c_i` of `D_{i+1}` joined to every vertex of `D_i` by an edge of weight
`5/4`; the partition `{D₀, D₁, D₂}` with centers `c_i` is a weak `(1, 5/4)`-neighborhood cover, and
no single dominating forest gives every edge of the cycles distance at most `5/2` (exhaustive
search, `MODERATION_NOTES.md`). With `2s` the proof goes through: in each partition, move one cluster
of every cycle of length at least 3 of the map `C ↦ (the cluster containing q(C))` to a second
forest; the stars of each of the two classes then form a forest. Strong covers and HST covers keep
`s`.

**Formalization Note.** The clustering is `Pi : Fin s → Finpartition univ`. `strong` says whether
it is a strong or a weak pairwise cover; `nbhd = true` adds the hypothesis that it is also a
`(∆, α)`-neighborhood cover. The conclusion is about one forest cover `F` and one HST cover `H`
carrying every applicable item. `∆ > 0` and `α > 0` are Definition 11's ranges. -/
theorem lemma_13 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (strong nbhd : Bool)
    (Δ α : ℝ) (s : ℕ) (Pi : Fin s → Finpartition (Finset.univ : Finset V))
    (hΔ : 0 < Δ) (hα : 0 < α) (hC : IsPairwiseCover G strong Δ α Pi)
    (hN : nbhd = true → IsNeighborhoodCover G strong Δ α Pi) :
    (∃ m ≤ (if strong = true then s else 2 * s), ∃ F : Fin m → WForest V,
        IsForestCover G F ∧ ForestScaleLE G F Δ (2 * α) ∧
        (strong = true → ∀ i, (F i).IsSpanning G) ∧
        (nbhd = true → ForestRamseyScale G F Δ (2 * α))) ∧
    (∃ m ≤ s, ∃ H : Fin m → HST V,
        IsHSTCover G H ∧ HSTScaleLE G H Δ (2 * α) ∧
        (nbhd = true → HSTRamseyScale G H Δ (2 * α))) := by sorry

end ARTreeCover
