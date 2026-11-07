-- Prove2me | Theorems.Thm_ARTreeCover_theorem_10
-- name    : ARTreeCover.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:36.13977+00:00
-- url     : https://prove2.me/theorems/480de967-5add-4ec7-b201-a83636a0112c
-- title:
--   Theorem 10: strong $(\Delta,k)$-probabilistic decompositions with parameter $\frac14 n^{-1/k}$
-- statement:
--   Let $G$ be an $n$-vertex weighted graph, $\Delta>0$ a real number and $k>0$ an integer. There is a distribution on partitions of $V$, all of whose clusters have strong radius at most $k\Delta$, such that for all $u,v$ with $d_G(u,v)\le\Delta$,
--
--   $$\Pr_{\Pi}[\exists C\in\Pi:\ u,v\in C]\ge\frac14\,n^{-1/k}.$$
--
--   This is the paper's new decomposition, with radius blow-up $k$ in place of the $k+1$ of Filtser (2019) and the same probability parameter up to a constant. It is the source of the stretch $(2+\epsilon)k$ of the goal.
--
--   Differences from the source:
--   - encoding: G = (V, E, w) with w : E → ℝ₊ and shortest-path distance d_G → `SimpleGraph` on a finite type with a weight on unordered pairs, positive on edges; d_G in [0, ∞], the infimum over walks, ∞ across components; reason: the same instances; the paper allows disconnected graphs (footnote 13, p.28) and positive weights make the infimum a minimum over paths
--   - encoding: a distribution D of partitions, with radius at most α∆ → a `PMF` on `Finpartition univ`; the radius bound holds on its support and probabilities are outer-measure values; reason: a finite type: every set is an event and the probability is the sum of point masses
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 10, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_IsProbabilisticDecomp

namespace ARTreeCover

/-- **Theorem 10**, p.12 (PDF p.15). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Any n-vertex undirected weighted graph G = (V, E) admits a strong (∆, k)-probabilistic
decomposition with probability parameter ¼n^{−1/k}, for any choice of a real parameter ∆ > 0 and
an integer parameter k > 0."

**Formalization Note.** `n = Fintype.card V`; the radius blow-up is `α = k` and the probability
parameter is exactly `¼ · n^{−1/k}` (`Real.rpow`). The distribution is over partitions of all of
`V`, and the strong radius bound `k∆` holds for every partition in its support. -/
theorem theorem_10 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (Δ : ℝ) (k : ℕ), 0 < Δ → 0 < k →
      ∃ D : PMF (Finpartition (Finset.univ : Finset V)),
        IsProbabilisticDecomp G true Δ k (1 / 4 * (Fintype.card V : ℝ) ^ (-(1 : ℝ) / k)) D := by sorry

end ARTreeCover
