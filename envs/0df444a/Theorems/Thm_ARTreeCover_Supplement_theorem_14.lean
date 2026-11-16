-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_14
-- name    : ARTreeCover.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:04:34.593198+00:00
-- url     : https://prove2.me/theorems/c607fe3b-7676-4906-bc5c-1a6a646ea790
-- title:
--   Theorem 14 — $K_r$-minor-free graphs have weak $O(r^{1/k}\log n)$-layered $(\Delta,O(k))$-neighborhood covers
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted $K_r$-minor-free graph and let $k\ge1$ and $\Delta>0$ be real numbers. Then $G$ admits a weak $s$-layered $(\Delta,Ck)$-neighborhood cover with
--   $$s\le C\,r^{1/k}\,L(n),\qquad L(n)=\max(1,\log_2 n).$$
--
--   The clusters have weak radius at most $Ck\Delta$. This is item 3 of Theorems 22 and 27 before the passage to tree covers.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 14, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_IsPairwiseCover
import Definitions.Def_ARTreeCover_Supplement_KrMinorFree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 14**, p.16 (PDF p.19). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Suppose that G = (V, E) is an n-vertex undirected weighted Kr-minor-free graph, and let k ≥ 1 and
∆ > 0 be real parameters. Then, G admits a weak O(r^{1/k} log n)-layered (∆, O(k))-neighborhood
cover."

**Formalization Note.**
1. One absolute `C > 0` (chosen before `V`, `G`, `r`, `k`, `∆`) serves both O(·): at most
   `C · r^{1/k} · L(n)` layers, radius blow-up `C · k`. `L(n) = max(1, log₂ n)`.
2. `k ≥ 1` is real, as printed; `r^{1/k}` is `Real.rpow`.
3. `K_r`-minor-free is `KrMinorFree r G`; for `r ≤ 1` it forces `V = ∅` or is unsatisfiable. -/
theorem theorem_14 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (r : ℕ) (k Δ : ℝ),
        1 ≤ k → 0 < Δ → KrMinorFree r G →
        ∃ s : ℕ, (s : ℝ) ≤ C * (r : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧
          ∃ Pi : Fin s → Finpartition (Finset.univ : Finset V),
            IsNeighborhoodCover G false Δ (C * k) Pi := by sorry

end ARTreeCover.Supplement
