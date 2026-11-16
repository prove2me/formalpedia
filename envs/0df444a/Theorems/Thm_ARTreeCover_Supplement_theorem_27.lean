-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_27
-- name    : ARTreeCover.Supplement.theorem_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:11:10.504058+00:00
-- url     : https://prove2.me/theorems/f08329a7-d67e-412f-a511-03a58ab7f7d7
-- title:
--   Theorem 27 — connected $K_r$-minor-free graphs have almost-Ramsey trees and HSTs: four stretch/count trade-offs
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a connected $n$-vertex weighted $K_r$-minor-free graph, $k>0$ an integer, $0<\epsilon\le1$, $\Delta>0$ and $L(n)=\max(1,\log_2n)$. For each of the following pairs $(\alpha,s)$, $G$ admits a (not necessarily spanning) almost-Ramsey tree $T$ and an almost-Ramsey HST $H$ for scale $\Delta$, each satisfying at least $n/s$ vertices with stretch $\alpha$:
--
--   1. $\alpha=8+\epsilon$ and $s=(C/\epsilon)^r$;
--   2. $\alpha=16+\epsilon$ and $s=C\,r^4/\epsilon^2$;
--   3. $\alpha=Ck$ and $s=C\,r^{1/k}L(n)$;
--   4. $\alpha=Cr$ and $s=C\,r^2$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - encoding: O(1/ϵ)^r → (C/ϵ)^r; reason: the constant sits inside the power as printed
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: a (not necessarily spanning) tree T = (V, E′) → a published WForest (weights in (0, ∞]) whose graph is preconnected; reason: on the nonempty vertex set of a connected graph this is a tree on V; edges outside G with any positive weight are allowed (footnote 13, p.28)
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 27, p.39 (PDF p.42)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_Supplement_KrMinorFree
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyTree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 27**, p.39 (PDF p.42). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G be a connected n-vertex Kr-minor-free graph, let k > 0 be an integer, and let 0 < ϵ ≤ 1 and
∆ > 0 be real parameters. Then, G admits a (not necessarily spanning) almost-Ramsey tree T and an
almost-Ramsey HST H for scale ∆, that satisfies n/s vertices with stretch α, for every choice of the
following pairs of values for α and s.
1. (Item (3) in Theorem 11) α = 8 + ϵ and s = O(1/ϵ)^r,
2. (Item (4) in Theorem 11) α = 16 + ϵ and s = O(r⁴/ϵ²),
3. (Theorem 14) α = O(k) and s = O(r^{1/k} log n),
4. (Item (2) in Theorem 11) α = O(r) and s = O(r²)."

**Formalization Note.**
1. One absolute `C > 0`, chosen before every other parameter, serves every O(·), including the
   stretches. `O(1/ϵ)^r` is `(C/ϵ)^r`, the constant inside the power as printed.
   `L(n) = max(1, log₂ n)`.
2. The tree is a published `WForest` with preconnected graph, not necessarily a subgraph of `G`.
   Each item is a separate pair (tree, HST). -/
theorem theorem_27 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (r k : ℕ) (ε Δ : ℝ),
        0 < k → 0 < ε → ε ≤ 1 → 0 < Δ → G.graph.Connected → KrMinorFree r G →
        ((∃ T : WForest V, IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / ((C / ε) ^ r)) (8 + ε)) ∧
          (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / ((C / ε) ^ r)) (8 + ε))) ∧
        ((∃ T : WForest V, IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ 4 / ε ^ 2)) (16 + ε)) ∧
          (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ 4 / ε ^ 2)) (16 + ε))) ∧
        ((∃ T : WForest V, IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k)) ∧
          (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k))) ∧
        ((∃ T : WForest V, IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ 2)) (C * r)) ∧
          (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ 2)) (C * r))) := by sorry

end ARTreeCover.Supplement
