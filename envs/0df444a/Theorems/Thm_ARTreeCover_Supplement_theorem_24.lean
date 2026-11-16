-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_24
-- name    : ARTreeCover.Supplement.theorem_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:09:15.643819+00:00
-- url     : https://prove2.me/theorems/b0f2227e-9aac-4ab2-bd24-f19628d85710
-- title:
--   Theorem 24 — connected graphs have a spanning almost-Ramsey tree and an almost-Ramsey HST satisfying $\Omega(n^{1-1/k}/k)$ vertices with stretch $4k-2$
-- statement:
--   There is an absolute constant $C>0$ such that for every real $\Delta>0$, every integer $k>0$ and every connected $n$-vertex weighted graph $G$, there are a spanning almost-Ramsey tree $T$ and an almost-Ramsey HST $H$ for scale $\Delta$, each satisfying at least
--   $$\frac{n^{1-1/k}}{Ck}$$
--   vertices with stretch $4k-2$.
--
--   Compared with spanning Ramsey trees, whose stretch is $\Omega(\log\log n)$, the stretch here is independent of $n$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 24, p.38 (PDF p.41)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyTree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 24**, p.38 (PDF p.41). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For every real parameter ∆ > 0 and every integer parameter k > 0, any n-vertex undirected weighted
connected graph G admits a spanning almost-Ramsey tree T and an almost-Ramsey HST H for scale ∆,
that satisfies Ω(1/k · n^{1−1/k}) vertices with stretch 4k − 2."

**Formalization Note.** `Ω(x)` is `x / C` with one absolute `C > 0` chosen before `V`, `G`, `∆`, `k`.
The tree and the HST are separate objects, each with its own set `S`; the tree is spanning
(`WForest.IsSpanning G`). Single almost-Ramsey trees and HSTs are `IsAlmostRamseyTree` and
`IsAlmostRamseyHST` (Definition 18). -/
theorem theorem_24 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (Δ : ℝ) (k : ℕ),
        0 < Δ → 0 < k → G.graph.Connected →
        (∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) ^ (1 - ((1 : ℝ) / k)) / (C * k)) (4 * (k : ℝ) - 2)) ∧
          (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) ^ (1 - ((1 : ℝ) / k)) / (C * k)) (4 * (k : ℝ) - 2)) := by sorry

end ARTreeCover.Supplement
