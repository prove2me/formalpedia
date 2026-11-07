-- Prove2me | Theorems.Thm_ARTreeCover_lemma_28
-- name    : ARTreeCover.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:14.690086+00:00
-- url     : https://prove2.me/theorems/a28fe0c2-6d1f-439f-8c80-74bc08928616
-- title:
--   Lemma 28: the aspect-ratio reduction for HST covers, $O(\epsilon^{-1}\log(n/\epsilon))$ scales
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $\epsilon\in(0,1]$, $\alpha\ge 1$ and $M$ a natural number. Suppose that for every $\Delta>0$ every minor $G^*$ of $G$ has an HST cover of size at most $M$ with scale-$\Delta$ stretch $\alpha$. Then $G$ has an HST cover of size at most $C\,M\,\epsilon^{-1}L(n/\epsilon)$ and stretch $(1+\epsilon)\alpha$. If moreover every such cover is Ramsey scale-$\Delta$, the resulting cover is almost-Ramsey with stretch $(1+\epsilon)\alpha$.
--
--   This is the analogue of Lemma 27 for ultrametrics, where a single HST is stretched less by the contraction.
--
--   Differences from the source:
--   - reading: the hypothesis "a scale-∆ HST cover H∗_∆ with size at most M(ϵ)", with no stretch → with size at most M and scale-∆ stretch at most α; reason: a scale-∆ HST cover is defined only with a stretch (Definition 16), α appears in the conclusion, and the proof says "has a scale-∆ HST cover H∗_∆ of size M(ϵ) and stretch α" (p.VI), as Lemma 12 states it
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log(n/ϵ) in the size bound → L(n/ϵ) = max(1, log₂(n/ϵ)); reason: equal for n/ϵ ≥ 2; at n = ϵ = 1 the printed bound is 0 while one HST is needed
--   - reading: M(ϵ) in the hypothesis and M(ϵ/3, ϵ/2) in the size bound → a fixed natural number `M` in both; reason: the printed form is the instance with the value of the function at the smaller parameter, and a fixed bound is a constant function; n is fixed with G
--   - reading: the "moreover" clauses, each about the cover F → Boolean flags in the hypothesis and the conclusion; one cover carries every clause whose flag is set; reason: the printed clauses are about the same F, and Theorem 19 needs a spanning almost-Ramsey forest cover
--   - reading: every minor G∗ of G (vertex deletions, edge deletions, edge contractions; p.9) → a branch-set minor H on any finite vertex type, each edge of H carrying the weight of a G-edge between its branch sets; reason: a contraction merges parallel edges by keeping one, and earlier deletions choose which; conversely every such choice arises by deleting the others; Appendix A uses exactly these minors
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: an HST is a rooted tree with labels (Definition 3) → the leaf set L(T) with the ultrametric ρ_T(x, y) = ℓ(LCA(x, y)), and ρ_T = ∞ off the leaves; reason: by the paper's sentence after Definition 3 and Fact 6 the leaf ultrametrics of HSTs are exactly the finite ultrametrics, and no statement uses the internal vertices; ∞ off the leaves lets d_G ≤ ρ_T be stated for all pairs of V
--   - reading: HST labels in ℝ≥0 (Definition 3) → ρ_T takes values in [0, ∞]; reason: the proof of Lemma 13 labels a root "diam(G) or ∞" (p.32); with finite labels the HST clauses fail on edgeless graphs, where d_G(u, v) = ∞ forces one leaf per HST and n HSTs
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Lemma 28, p.VI (PDF p.65)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WMinor
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover

namespace ARTreeCover

/-- **Lemma 28**, p.VI (PDF p.65). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex undirected weighted graph, and let ϵ ∈ (0, 1] and α ≥ 1 be real
parameters. Suppose that, for every ∆ > 0, every minor G∗ = (V∗, E∗) of G admits a scale-∆ HST
cover H∗_∆ with size at most M(ϵ). Then, G admits an HST cover H with size at most
M(ϵ/3) · O(1/ϵ log n/ϵ) and stretch (1 + ϵ)α. Moreover, if for every ∆ > 0 and every minor G∗ the
HST cover H∗_∆ is a Ramsey scale-∆ HST cover, then H is an almost-Ramsey HST cover with size
M(ϵ/2) · O(1/ϵ log n/ϵ) and stretch (1 + ϵ)α."

**Formalization Note.**
1. The hypothesis carries "and stretch at most α", which the printed hypothesis omits: a scale-∆
   HST cover is defined only with a stretch (Definition 16), and the proof uses it ("has a
   scale-∆ HST cover H∗_∆ of size M(ϵ) and stretch α", p.VI), as Lemma 12 states it.
2. Minors, the fixed bound `M`, `C`, `L` and the flag `ramsey` are as in `lemma_27`. -/
theorem lemma_28 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (ε α : ℝ) (M : ℕ) (ramsey : Bool),
        0 < ε → ε ≤ 1 → 1 ≤ α →
        (∀ Δ : ℝ, 0 < Δ → ∀ (W : Type) [Fintype W] (H : WGraph W), WMinor H G →
          ∃ m ≤ M, ∃ T : Fin m → HST W,
            IsHSTCover H T ∧ HSTScaleLE H T Δ α ∧
            (ramsey = true → HSTRamseyScale H T Δ α)) →
        ∃ m : ℕ, (m : ℝ) ≤ C * M * ε⁻¹ * logL ((Fintype.card V : ℝ) / ε) ∧
          ∃ T : Fin m → HST V,
            IsHSTCover G T ∧ HSTStretchLE G T ((1 + ε) * α) ∧
            (ramsey = true → HSTAlmostRamsey G T ((1 + ε) * α)) := by sorry

end ARTreeCover
