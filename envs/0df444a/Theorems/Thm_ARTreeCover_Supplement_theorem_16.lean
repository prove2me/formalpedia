-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_16
-- name    : ARTreeCover.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:05:59.998901+00:00
-- url     : https://prove2.me/theorems/2dc6bec9-5d8d-4689-9e57-b2d55e2a10c7
-- title:
--   Theorem 16 — $p$-path-separable graphs: $(\lceil4/\epsilon\rceil+3)p\log n$-layered strong pairwise and neighborhood covers (corrected: $\max(1,\log_2 n)$)
-- statement:
--   Let $\Delta,\epsilon>0$ and let $G$ be an $n$-vertex weighted $p$-path-separable graph. Then $G$ has an $s$-layered clustering $\mathcal C$ with
--   $$s\le\left(\left\lceil\tfrac4\epsilon\right\rceil+3\right)p\,L(n),\qquad L(n)=\max(1,\log_2 n),$$
--   which is at the same time a strong $(\Delta,1+\epsilon/2)$-pairwise cover and a strong $(\Delta/2,2+\epsilon)$-neighborhood cover.
--
--   The constants are explicit. This is the source of the stretch-$(4+\epsilon)$ almost-Ramsey trees of Theorem 25.
--
--   Differences from the source:
--   - correction: (⌈4/ϵ⌉ + 3) p log n layers → (⌈4/ϵ⌉ + 3) p max(1, log₂ n) layers; reason: at n = 1 the printed bound is 0 layers, but the one-vertex graph, which is 1-path-separable, needs one layer for the pair (u, u); for n ≥ 2 nothing changes
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 16, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_IsPairwiseCover
import Definitions.Def_ARTreeCover_Supplement_HasPathSep

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 16**, p.18 (PDF p.21). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Fix some positive parameters ∆, ϵ > 0. Every n-vertex p-path-separable graph G = (V, E) has a
(⌈4/ϵ⌉ + 3) p log n-layered clustering C, which is both a strong (∆, 1 + ϵ/2)-pairwise cover and a
strong (∆/2, 2 + ϵ)-neighborhood cover."

**Formalization Note.**
1. The explicit bound is kept, with `log n` read as `L(n) = max(1, log₂ n)`: at `n = 1` the printed
   bound is `0` layers, but a one-vertex graph needs one (correction; see the item's differences).
2. One clustering `Pi` carries both properties. `p`-path-separable means weakly
   (`IsPPathSeparable G p false`). Every `ϵ > 0` and `∆ > 0`. -/
theorem theorem_16 (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (p : ℕ) (Δ ε : ℝ)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hG : IsPPathSeparable G p false) :
    ∃ s : ℕ, (s : ℝ) ≤ ((⌈4 / ε⌉₊ : ℝ) + 3) * p * logL (Fintype.card V) ∧
      ∃ Pi : Fin s → Finpartition (Finset.univ : Finset V),
        IsPairwiseCover G true Δ (1 + ε / 2) Pi ∧
          IsNeighborhoodCover G true (Δ / 2) (2 + ε) Pi := by sorry

end ARTreeCover.Supplement
