-- Prove2me | Theorems.Thm_ARTreeCover_theorem_11_item_1
-- name    : ARTreeCover.theorem_11_item_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:59.852259+00:00
-- url     : https://prove2.me/theorems/de2308f2-cd31-47ff-8244-edeffc72ea0d
-- title:
--   Theorem 11, Item 1: strong $O(kn^{1/k})$-layered $(\Delta,2k-1)$-neighborhood covers
-- statement:
--   There is an absolute constant $C>0$ such that for every $n$-vertex weighted graph $G$, every real $\Delta>0$ and every integer $k\ge 1$ there is $s\le C\,k\,n^{1/k}$ and an $s$-layered strong $(\Delta,2k-1)$-neighborhood cover of $G$.
--
--   The result is due to Awerbuch and Peleg (1990). Together with Lemma 14 it gives the almost-Ramsey clauses of the goal.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - encoding: "let ∆, ϵ > 0 be real parameters" in the preamble of Theorem 11 → no ϵ; reason: ϵ does not occur in Item 1; it serves the other items
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: an s-layered clustering C = Π₁ ∪ … ∪ Π_s (Definition 1) → a family of s partitions of V (`Fin s → Finpartition univ`), repetitions allowed; reason: the clusters are the parts; a clustering with fewer layers is s-layered by repeating a layer
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 11, Item 1, p.15 (PDF p.18); restated and proved in Appendix C, pp.XVI–XVII (PDF pp.75–76)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_IsPairwiseCover

namespace ARTreeCover

/-- **Theorem 11, Item 1**, p.15 (PDF p.18); restated and proved in Appendix C, pp.XVI–XVII
(PDF pp.75–76). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex undirected weighted graph, let k ≥ 1 be an integer parameter, and
let ∆, ϵ > 0 be real parameters. 1. ([11]) The graph G admits a strong O(kn^{1/k})-layered strong
(∆, 2k − 1)-neighborhood cover". Appendix C: "Any n-vertex undirected weighted graph G = (V, E)
admits an O(kn^{1/k})-layered strong (∆, 2k − 1)-neighborhood cover, for any choice of a real
parameter ∆ > 0 and an integer parameter k > 0."

**Formalization Note.** `O(kn^{1/k})` is `C · k · n^{1/k}` with one absolute `C > 0` chosen before
`V`, `G`, `∆`, `k`. The parameter `ϵ` of the theorem's preamble does not occur in Item 1 and is
omitted. -/
theorem theorem_11_item_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (Δ : ℝ) (k : ℕ), 0 < Δ → 1 ≤ k →
        ∃ s : ℕ, (s : ℝ) ≤ C * k * (Fintype.card V : ℝ) ^ ((1 : ℝ) / k) ∧
          ∃ Pi : Fin s → Finpartition (Finset.univ : Finset V),
            IsNeighborhoodCover G true Δ (2 * k - 1) Pi := by sorry

end ARTreeCover
