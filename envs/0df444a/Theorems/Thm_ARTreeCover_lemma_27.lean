-- Prove2me | Theorems.Thm_ARTreeCover_lemma_27
-- name    : ARTreeCover.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:57:22.397198+00:00
-- url     : https://prove2.me/theorems/19aba615-5acb-4f28-ab91-0471d882aad7
-- title:
--   Lemma 27: the aspect-ratio reduction for forest covers, $O(\epsilon^{-1}\log(n/\epsilon))$ scales
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $\epsilon\in(0,1]$, $\alpha\ge 1$ and $M$ a natural number. Suppose that for every $\Delta>0$ every minor $G^*$ of $G$ has a forest cover of size at most $M$ with scale-$\Delta$ stretch $\alpha$. Then $G$ has a forest cover of size at most $C\,M\,\epsilon^{-1}L(n/\epsilon)$ and stretch $(1+\epsilon)\alpha$. Moreover:
--
--   1. if every such cover is Ramsey scale-$\Delta$, the resulting cover is almost-Ramsey with stretch $(1+\epsilon)\alpha$;
--   2. if every such cover is spanning, the resulting cover is spanning.
--
--   The hypothesis is about every minor, not about $G$ alone: the proof contracts light edges and deletes heavy ones at each scale. This removes the dependence on the aspect ratio of $G$.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log(n/ϵ) in the size bound → L(n/ϵ) = max(1, log₂(n/ϵ)); reason: equal for n/ϵ ≥ 2; at n = ϵ = 1 the printed bound is 0 while one forest is needed
--   - reading: M(ϵ) in the hypothesis and M(ϵ/5, ϵ/2) in the size bound → a fixed natural number `M` in both; reason: the printed form is the instance with the value of the function at the smaller parameter, and a fixed bound is a constant function; n is fixed with G
--   - reading: the "moreover" clauses, each about the cover F → Boolean flags in the hypothesis and the conclusion; one cover carries every clause whose flag is set; reason: the printed clauses are about the same F, and Theorem 19 needs a spanning almost-Ramsey forest cover
--   - reading: every minor G∗ of G (vertex deletions, edge deletions, edge contractions; p.9) → a branch-set minor H on any finite vertex type, each edge of H carrying the weight of a G-edge between its branch sets; reason: a contraction merges parallel edges by keeping one, and earlier deletions choose which; conversely every such choice arises by deleting the others; Appendix A uses exactly these minors
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: forests with V(F) ⊆ V and weights in (0, ∞] → a forest on all of V; a vertex outside V(F) is isolated; reason: this changes no distance between distinct vertices and gives d_F(u, u) = 0, which the paper assumes (p.31)
--   - reading: spanning: E(F) ⊆ E → every edge of F is an edge of G and carries G's weight; reason: a forest whose edges are edges of G but with other weights is not a subgraph of the weighted graph G
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Lemma 27, p.I (PDF p.60)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WMinor
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover

namespace ARTreeCover

/-- **Lemma 27**, p.I (PDF p.60). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex undirected weighted graph, and let ϵ ∈ (0, 1] and α ≥ 1 be real
parameters. Suppose that, for every ∆ > 0, every minor G∗ = (V∗, E∗) of G admits a scale-∆ forest
cover F∗_∆ with size at most M(ϵ) and stretch at most α. Then, G admits a forest cover F with size
M(ϵ/5) · O(1/ϵ log n/ϵ) and stretch (1 + ϵ)α. Moreover, if for every ∆ > 0 and every minor G∗ the
forest cover F∗_∆ is a Ramsey scale-∆ forest cover, then F is a almost-Ramsey forest cover with
size M(ϵ/2) · O(1/ϵ log n/ϵ) and stretch (1 + ϵ)α. If for every minor G∗ and ∆ the forest cover
F∗_∆ is spanning, then F is a spanning forest cover for G."

**Formalization Note.**
1. Minors are weighted minors on any finite vertex type (`WMinor`).
2. The size bound `M(·)` of the hypothesis is a fixed natural number `M` and the conclusion's size
   is `C · M · ϵ⁻¹ · L(n/ϵ)` with one absolute `C > 0` chosen before everything else and
   `L(x) = max(1, log₂ x)`. Instantiating `M := M(ϵ/5)` (resp. `M(ϵ/2)`) gives the printed form.
3. The flags `ramsey` and `spanning` add the "Moreover" hypotheses; one cover `F` carries every
   applicable conclusion (the goal needs a spanning almost-Ramsey cover). -/
theorem lemma_27 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (ε α : ℝ) (M : ℕ) (ramsey spanning : Bool),
        0 < ε → ε ≤ 1 → 1 ≤ α →
        (∀ Δ : ℝ, 0 < Δ → ∀ (W : Type) [Fintype W] (H : WGraph W), WMinor H G →
          ∃ m ≤ M, ∃ F : Fin m → WForest W,
            IsForestCover H F ∧ ForestScaleLE H F Δ α ∧
            (ramsey = true → ForestRamseyScale H F Δ α) ∧
            (spanning = true → ∀ i, (F i).IsSpanning H)) →
        ∃ m : ℕ, (m : ℝ) ≤ C * M * ε⁻¹ * logL ((Fintype.card V : ℝ) / ε) ∧
          ∃ F : Fin m → WForest V,
            IsForestCover G F ∧ ForestStretchLE G F ((1 + ε) * α) ∧
            (ramsey = true → ForestAlmostRamsey G F ((1 + ε) * α)) ∧
            (spanning = true → ∀ i, (F i).IsSpanning G) := by sorry

end ARTreeCover
