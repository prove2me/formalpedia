-- Prove2me | Theorems.Thm_ARTreeCover_lemma_2
-- name    : ARTreeCover.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:49.214943+00:00
-- url     : https://prove2.me/theorems/ca55ba46-26db-4d41-864b-897cfbc59229
-- title:
--   Lemma 2: decompositions give $O(\log n/p)$-layered covers
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $\Delta,\alpha>0$ and $0<p\le 1$. If $D$ is a strong (respectively, weak) $(\Delta,\alpha)$-probabilistic decomposition of $G$ with probability parameter $p$, then there is $s\le C\,L(n)/p$ and an $s$-layered strong (respectively, weak) $(\Delta,\alpha)$-pairwise cover. If moreover $D$ is a $(\Delta,\alpha)$-padded decomposition with parameter $p$, this clustering is also a $(\Delta,\alpha)$-neighborhood cover.
--
--   This is the folklore reduction from random partitions to deterministic layered covers.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log n in the size bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, while a one-vertex graph needs at least one forest or layer for the pair (u, u)
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: a distribution D of partitions, with radius at most α∆ → a `PMF` on `Finpartition univ`; the radius bound holds on its support and probabilities are outer-measure values; reason: a finite type: every set is an event and the probability is the sum of point masses
--   - encoding: an s-layered clustering C = Π₁ ∪ … ∪ Π_s (Definition 1) → a family of s partitions of V (`Fin s → Finpartition univ`), repetitions allowed; reason: the clusters are the parts; a clustering with fewer layers is s-layered by repeating a layer
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Lemma 2, p.16 (PDF p.19); proof in Appendix D, pp.XVII–XVIII (PDF pp.76–77)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_IsPairwiseCover
import Definitions.Def_ARTreeCover_IsProbabilisticDecomp

namespace ARTreeCover

/-- **Lemma 2**, p.16 (PDF p.19); proof in Appendix D, pp.XVII–XVIII (PDF pp.76–77). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Suppose that the graph G = (V, E) admits a strong (respectively, weak) (∆, α)-probabilistic
decomposition D with probability parameter p. Then, G also admits a strong (rep., weak)
O(log n / p)-layered (∆, α)-pairwise cover C. Moreover, if D is a strong (respectively, weak)
(∆, α)-padded decomposition with probability parameter p, then C is a strong (resp., weak)
O(log n / p)-layered (∆, α)-neighborhood cover."

**Formalization Note.** `strong = true` is the strong variant, `strong = false` the weak one.
`O(log n / p)` is `C · L(n) / p` with one absolute `C > 0` chosen before the graph and all
parameters, and `L(n) = max(1, log₂ n)` (`logL`). The ranges `∆ > 0`, `α > 0`, `0 < p ≤ 1` are
Definition 10's. Since a padded decomposition is a probabilistic one (p.12), the "Moreover" is the
implication from `IsPaddedDecomp` to the neighborhood property of the same clustering. -/
theorem lemma_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (strong : Bool) (Δ α p : ℝ)
        (D : PMF (Finpartition (Finset.univ : Finset V))),
        0 < Δ → 0 < α → 0 < p → p ≤ 1 →
        IsProbabilisticDecomp G strong Δ α p D →
        ∃ s : ℕ, (s : ℝ) ≤ C * logL (Fintype.card V) / p ∧
          ∃ Pi : Fin s → Finpartition (Finset.univ : Finset V),
            IsPairwiseCover G strong Δ α Pi ∧
            (IsPaddedDecomp G strong Δ α p D → IsNeighborhoodCover G strong Δ α Pi) := by sorry

end ARTreeCover
