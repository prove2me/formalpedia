-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_12
-- name    : ARTreeCover.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:03:59.533518+00:00
-- url     : https://prove2.me/theorems/0e37399e-5f92-4ab0-9a6c-3f05a7048f45
-- title:
--   Theorem 12 — doubling dimension $d$ gives strong $O(d^{1/k}\log n)$-layered $(\Delta,O(k))$-neighborhood covers (corrected: $d$ read as $\max(1,d)$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G=(V,E)$ be an $n$-vertex weighted graph, $k\ge1$ an integer and $\Delta>0$. If the shortest-path metric of $G$ has doubling dimension at most $d$, then $G$ admits a strong $s$-layered $(\Delta,Ck)$-neighborhood cover with
--   $$s\le C\,\max(1,d)^{1/k}\,L(n),\qquad L(n)=\max(1,\log_2 n).$$
--
--   Every cluster has strong radius at most $Ck\Delta$ and every ball $B_G(u,\Delta)$ lies inside one cluster. Through Lemma 14 this gives the doubling-dimension clause of Theorem 23.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - correction: d^{1/k} (doubling dimension at most d) inside O(·) → max(1, d)^{1/k}; reason: a one-vertex graph has doubling dimension 0, and with d = 0 the bound d^{1/k} = 0 allows no layer or tree, while a cover needs one; for d ≥ 1 nothing changes
--   - encoding: doubling dimension of the induced metric (V, d_G) → DoublingDimLE on the extended distance d_G with closed balls centred at vertices; reason: the same metric; d_G = ∞ across components keeps every ball inside one component
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 12, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_IsPairwiseCover
import Definitions.Def_ARTreeCover_Supplement_DoublingDimLE

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 12**, p.16 (PDF p.19). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex undirected weighted graph, let k ≥ 1 be an integer parameter, and
let ∆ > 0 be a real parameter. If the induced metric of G has doubling dimension at most d, then G
admits a strong O(d^{1/k} · log n)-layered (∆, O(k))-neighborhood cover."

**Formalization Note.**
1. One absolute `C > 0` (chosen before `V`, `G`, `k`, `∆`, `d`) serves both O(·): at most
   `C · max(1, d)^{1/k} · L(n)` layers, radius blow-up `C · k`. `L(n) = max(1, log₂ n)`.
2. `d` is clamped to `max(1, d)` inside O(·): a one-vertex graph has doubling dimension `0`, where
   `0^{1/k} = 0` would allow no layer, while a cover needs one.
3. Doubling dimension is `DoublingDimLE` on the extended metric `d_G` (closed balls); layered
   neighborhood covers are the published `IsNeighborhoodCover` with `strong = true`. -/
theorem theorem_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (k : ℕ) (Δ d : ℝ),
        1 ≤ k → 0 < Δ → DoublingDimLE G d →
        ∃ s : ℕ, (s : ℝ) ≤ C * (max 1 d) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧
          ∃ Pi : Fin s → Finpartition (Finset.univ : Finset V),
            IsNeighborhoodCover G true Δ (C * k) Pi := by sorry

end ARTreeCover.Supplement
