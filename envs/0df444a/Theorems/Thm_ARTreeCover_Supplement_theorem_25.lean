-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_25
-- name    : ARTreeCover.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:09:55.478907+00:00
-- url     : https://prove2.me/theorems/f142f33c-8099-4044-be82-885d98f70eac
-- title:
--   Theorem 25 — connected $p$-path-separable graphs have a spanning almost-Ramsey tree and HST with stretch $4+\epsilon$ (corrected: $\min(\epsilon,1)$ in the count)
-- statement:
--   There is an absolute constant $C>0$ such that for all real $\Delta,\epsilon>0$ and every connected $n$-vertex weighted $p$-path-separable graph $G$, there are a spanning almost-Ramsey tree $T$ and an almost-Ramsey HST $H$ for scale $\Delta$, each satisfying at least
--   $$\frac{\min(\epsilon,1)\,n}{C\,p\,L(n)},\qquad L(n)=\max(1,\log_2n),$$
--   vertices with stretch $4+\epsilon$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - correction: Ω(ϵn/(p log n)) satisfied vertices for every ϵ > 0 → ϵ replaced by min(ϵ, 1) in the count; the stretch keeps ϵ; reason: as printed, for any constant c the two-vertex graph with one edge (1-path-separable) would need more than 2 satisfied vertices once ϵ > 1/c; for ϵ ≤ 1 the statement is the printed one, and for ϵ > 1 it follows from ϵ = 1 because a larger stretch is weaker
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 25, p.38 (PDF p.41)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_Supplement_HasPathSep
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyTree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 25**, p.38 (PDF p.41). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For every real parameters ∆, ϵ > 0, any n-vertex connected p-path-separable graph G admits a
spanning almost-Ramsey tree T and an almost-Ramsey HST H for scale ∆, that satisfies
Ω(ϵn/(p log n)) vertices with stretch 4 + ϵ."

**Formalization Note.**
1. `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other parameter.
   `L(n) = max(1, log₂ n)`.
2. Correction: in the count, `ϵ` is replaced by `min(ϵ, 1)` (the stretch keeps `ϵ`). As printed for
   every `ϵ > 0` the count exceeds `n` when `ϵ → ∞`; for `ϵ ≤ 1` it is the printed statement.
3. `p`-path-separable means weakly (`IsPPathSeparable G p false`). -/
theorem theorem_25 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (p : ℕ) (Δ ε : ℝ),
        0 < Δ → 0 < ε → G.graph.Connected → IsPPathSeparable G p false →
        (∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ (min ε 1 * (Fintype.card V : ℝ) / (C * p * logL (Fintype.card V))) (4 + ε)) ∧
          (∃ H : HST V, IsAlmostRamseyHST G H Δ (min ε 1 * (Fintype.card V : ℝ) / (C * p * logL (Fintype.card V))) (4 + ε)) := by sorry

end ARTreeCover.Supplement
