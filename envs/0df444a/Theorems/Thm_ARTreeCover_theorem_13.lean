-- Prove2me | Theorems.Thm_ARTreeCover_theorem_13
-- name    : ARTreeCover.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:59.654735+00:00
-- url     : https://prove2.me/theorems/918b94be-9f00-4b99-9816-91087039aae2
-- title:
--   Theorem 13: strong $O(n^{1/k}\log n)$-layered $(\Delta,k)$-pairwise covers
-- statement:
--   There is an absolute constant $C>0$ such that for every $n$-vertex weighted graph $G$, every real $\Delta>0$ and every integer $k>0$ there is $s\le C\,n^{1/k}L(n)$ and an $s$-layered strong $(\Delta,k)$-pairwise cover of $G$.
--
--   Together with Lemma 14 this gives the stretch-$(2+\epsilon)k$ clauses of the goal.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: log n in the size bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, while a one-vertex graph needs at least one forest or layer for the pair (u, u)
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: an s-layered clustering C = Π₁ ∪ … ∪ Π_s (Definition 1) → a family of s partitions of V (`Fin s → Finpartition univ`), repetitions allowed; reason: the clusters are the parts; a clustering with fewer layers is s-layered by repeating a layer
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 13, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_IsPairwiseCover

namespace ARTreeCover

/-- **Theorem 13**, p.16 (PDF p.19). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Any n-vertex undirected weighted graph G = (V, E) admits a strong O(n^{1/k} log n)-layered
(∆, k)-pairwise cover, for any choice of a real parameter ∆ > 0 and an integer parameter k > 0."

**Formalization Note.** `O(n^{1/k} log n)` is `C · n^{1/k} · L(n)` with one absolute `C > 0` chosen
before `V`, `G`, `∆` and `k`; `L(n) = max(1, log₂ n)`; `n^{1/k}` is `Real.rpow`. -/
theorem theorem_13 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (Δ : ℝ) (k : ℕ), 0 < Δ → 0 < k →
        ∃ s : ℕ, (s : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧
          ∃ Pi : Fin s → Finpartition (Finset.univ : Finset V),
            IsPairwiseCover G true Δ k Pi := by sorry

end ARTreeCover
