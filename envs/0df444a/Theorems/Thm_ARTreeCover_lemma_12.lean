-- Prove2me | Theorems.Thm_ARTreeCover_lemma_12
-- name    : ARTreeCover.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:09.71324+00:00
-- url     : https://prove2.me/theorems/60bd406b-858c-4bbd-a3f2-4e4a3fb5a573
-- title:
--   Lemma 12: scale covers of all minors give covers of size $M\cdot O(\epsilon^{-1}\log n)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $\epsilon\in(0,1]$, $\alpha\ge 1$ and $M$ a natural number.
--
--   1. **Forests.** If for every $\Delta>0$ every minor of $G$ has a forest cover of size at most $M$ with scale-$\Delta$ stretch $\alpha$, then $G$ has a forest cover of size at most $C\,M\,\epsilon^{-1}L(n)$ and stretch $(1+\epsilon)\alpha$. If these covers are all Ramsey scale-$\Delta$, the result is almost-Ramsey with stretch $(1+\epsilon)\alpha$. If they are all spanning, the result is spanning.
--   2. **HSTs.** If for every $\Delta>0$ every minor of $G$ has an HST cover of size at most $M$ with scale-$\Delta$ stretch $\alpha$, then $G$ has an HST cover of size at most $C\,M\,\epsilon^{-1}L(n)$ and stretch $(1+\epsilon)\alpha$. If these covers are all Ramsey scale-$\Delta$, the result is almost-Ramsey with stretch $(1+\epsilon)\alpha$.
--
--   There is no lower bound on $\epsilon$: Remark 3 of the paper treats $\epsilon<1/n^2$ by a cover of size at most $n^2$.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log n in the size bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, while a one-vertex graph needs at least one forest or layer for the pair (u, u)
--   - reading: M(ϵ) in the hypothesis and M(ϵ/5, ϵ/2) in the size bound → a fixed natural number `M` in both; reason: the printed form is the instance with the value of the function at the smaller parameter, and a fixed bound is a constant function; n is fixed with G
--   - reading: the "moreover" clauses, each about the cover F → Boolean flags in the hypothesis and the conclusion; one cover carries every clause whose flag is set; reason: the printed clauses are about the same F, and Theorem 19 needs a spanning almost-Ramsey forest cover
--   - reading: every minor G∗ of G (vertex deletions, edge deletions, edge contractions; p.9) → a branch-set minor H on any finite vertex type, each edge of H carrying the weight of a G-edge between its branch sets; reason: a contraction merges parallel edges by keeping one, and earlier deletions choose which; conversely every such choice arises by deleting the others; Appendix A uses exactly these minors
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: forests with V(F) ⊆ V and weights in (0, ∞] → a forest on all of V; a vertex outside V(F) is isolated; reason: this changes no distance between distinct vertices and gives d_F(u, u) = 0, which the paper assumes (p.31)
--   - reading: spanning: E(F) ⊆ E → every edge of F is an edge of G and carries G's weight; reason: a forest whose edges are edges of G but with other weights is not a subgraph of the weighted graph G
--   - encoding: an HST is a rooted tree with labels (Definition 3) → the leaf set L(T) with the ultrametric ρ_T(x, y) = ℓ(LCA(x, y)), and ρ_T = ∞ off the leaves; reason: by the paper's sentence after Definition 3 and Fact 6 the leaf ultrametrics of HSTs are exactly the finite ultrametrics, and no statement uses the internal vertices; ∞ off the leaves lets d_G ≤ ρ_T be stated for all pairs of V
--   - reading: HST labels in ℝ≥0 (Definition 3) → ρ_T takes values in [0, ∞]; reason: the proof of Lemma 13 labels a root "diam(G) or ∞" (p.32); with finite labels the HST clauses fail on edgeless graphs, where d_G(u, v) = ∞ forces one leaf per HST and n HSTs
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Lemma 12, p.31 (PDF p.34), with Remark 3, p.IX (PDF p.68)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WMinor
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover

namespace ARTreeCover

/-- **Lemma 12**, p.31 (PDF p.34), with Remark 3, p.IX (PDF p.68). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex undirected weighted graph, and let ϵ ∈ (0, 1] and α ≥ 1 be real
parameters. Suppose that, for every ∆ > 0, every minor G∗ = (V∗, E∗) of G admits a scale-∆ forest
cover F∗_∆ (respectively, a scale-∆ HST cover H∗_∆) with size at most M(ϵ) and stretch at most α.
Then, G admits a forest cover F (resp., an HST cover H) with size M(ϵ/5) · O(1/ϵ log n) and stretch
(1 + ϵ)α. Moreover, if for every ∆ > 0 and every minor G∗ the forest cover F∗_∆ is a Ramsey
scale-∆ forest cover, then F is an almost-Ramsey forest cover with size M(ϵ/2) · O(1/ϵ log n) and
stretch (1 + ϵ)α. Similarly, if H∗_∆ is a Ramsey scale-∆ HST cover, for every ∆ > 0 and minor G∗,
then H is an almost-Ramsey HST cover with size M(ϵ/2) · O(1/ϵ log n) and stretch (1 + ϵ)α. In the
results above, if for every ∆ > 0 and minor G∗, the forest cover F∗_∆ is a spanning, then F is a
spanning forest cover as well."

The first conjunct is the forest part, the second the HST part.

**Formalization Note.** Minors, the fixed bound `M`, `C` and the flags are as in `lemma_27`; the
size is `C · M · ϵ⁻¹ · L(n)` with `L(n) = max(1, log₂ n)`. No lower bound on `ϵ` is assumed:
the case `ϵ < 1/n²` is part of the lemma (Remark 3). -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (ε α : ℝ) (M : ℕ),
        0 < ε → ε ≤ 1 → 1 ≤ α →
        (∀ ramsey spanning : Bool,
          (∀ Δ : ℝ, 0 < Δ → ∀ (W : Type) [Fintype W] (H : WGraph W), WMinor H G →
            ∃ m ≤ M, ∃ F : Fin m → WForest W,
              IsForestCover H F ∧ ForestScaleLE H F Δ α ∧
              (ramsey = true → ForestRamseyScale H F Δ α) ∧
              (spanning = true → ∀ i, (F i).IsSpanning H)) →
          ∃ m : ℕ, (m : ℝ) ≤ C * M * ε⁻¹ * logL (Fintype.card V) ∧
            ∃ F : Fin m → WForest V,
              IsForestCover G F ∧ ForestStretchLE G F ((1 + ε) * α) ∧
              (ramsey = true → ForestAlmostRamsey G F ((1 + ε) * α)) ∧
              (spanning = true → ∀ i, (F i).IsSpanning G)) ∧
        (∀ ramsey : Bool,
          (∀ Δ : ℝ, 0 < Δ → ∀ (W : Type) [Fintype W] (H : WGraph W), WMinor H G →
            ∃ m ≤ M, ∃ T : Fin m → HST W,
              IsHSTCover H T ∧ HSTScaleLE H T Δ α ∧
              (ramsey = true → HSTRamseyScale H T Δ α)) →
          ∃ m : ℕ, (m : ℝ) ≤ C * M * ε⁻¹ * logL (Fintype.card V) ∧
            ∃ T : Fin m → HST V,
              IsHSTCover G T ∧ HSTStretchLE G T ((1 + ε) * α) ∧
              (ramsey = true → HSTAlmostRamsey G T ((1 + ε) * α))) := by sorry

end ARTreeCover
